/**
 * Cryptonote Node.JS Pool
 * https://github.com/dvandal/cryptonote-nodejs-pool
 *
 * Pool TCP daemon
 **/

// Load required modules
let fs = require('fs');
let net = require('net');
let tls = require('tls');
let async = require('async');
let bignum = require('bignum');

let apiInterfaces = require('./apiInterfaces.js')(config.daemon, config.wallet, config.api);
let notifications = require('./notifications.js');
let utils = require('./utils.js');

config.hashingUtil = config.hashingUtil || false;
let cnHashing = require('cryptonight-hashing');
if (config.hashingUtil) {
	cnHashing = require('turtlecoin-multi-hashing');
}
// Set nonce pattern - must exactly be 8 hex chars
let noncePattern = new RegExp("^[0-9A-Fa-f]{8}$");

// Set redis database cleanup interval
let cleanupInterval = config.redis.cleanupInterval && config.redis.cleanupInterval > 0 ? config.redis.cleanupInterval : 15;
let fallBackCoin = typeof config.poolServer.fallBackCoin !== 'undefined' && config.poolServer.fallBackCoin ? config.poolServer.fallBackCoin : 0

// Initialize log system
let logSystem = 'pool';
require('./exceptionWriter.js')(logSystem);

let threadId = '(Thread ' + process.env.forkId + ') ';
let log = function (severity, system, text, data) {
	global.log(severity, system, threadId + text, data);
};

// Set cryptonight algorithm
let cnAlgorithm = config.cnAlgorithm || "cryptonight";
let cnVariant = config.cnVariant || 0;
let cnBlobType = config.cnBlobType || 0;
let BlockTemplate = global.coinFuncs.BlockTemplate;

let cryptoNight;
if (!cnHashing || !cnHashing[cnAlgorithm]) {
	log('error', logSystem, 'Invalid cryptonight algorithm: %s', [cnAlgorithm]);
} else {
	cryptoNight = cnHashing[cnAlgorithm];
}

// Set instance id
let instanceId = utils.instanceId();

// Pool variables
let poolStarted = false;
let connectedMiners = {};
// Get merged mining tag reseved space size
let POOL_NONCE_SIZE = 16 + 1; // +1 for old XMR/new TRTL bugs
let EXTRA_NONCE_TEMPLATE = "02" + POOL_NONCE_SIZE.toString(16) + "00".repeat(POOL_NONCE_SIZE);
let mergedMining = false

function randomIntFromInterval (min, max) {
	return Math.floor(Math.random() * (max - min + 1) + min);
}

// Pool settings
let shareTrustEnabled = config.poolServer.shareTrust && config.poolServer.shareTrust.enabled;
let shareTrustStepFloat = shareTrustEnabled ? config.poolServer.shareTrust.stepDown / 100 : 0;
let shareTrustMinFloat = shareTrustEnabled ? config.poolServer.shareTrust.min / 100 : 0;

let banningEnabled = config.poolServer.banning && config.poolServer.banning.enabled;
let bannedIPs = {};
let perIPStats = {};

let slushMiningEnabled = config.poolServer.slushMining && config.poolServer.slushMining.enabled;

if (!config.poolServer.paymentId) {
	config.poolServer.paymentId = {};
}
if (!config.poolServer.paymentId.addressSeparator) {
	config.poolServer.paymentId.addressSeparator = "+";
}

if (config.poolServer.paymentId.validation == null) {
	config.poolServer.paymentId.validation = true;
}
if (config.poolServer.paymentId.ban == null) {
	config.poolServer.paymentId.ban = false;
}
if (config.poolServer.paymentId.validations == null) {
	config.poolServer.paymentId.validations = [];
	config.poolServer.paymentId.validation = false;
}

config.isRandomX = config.isRandomX || false;

let previousOffset = config.previousOffset || 7;
let offset = config.offset || 2;
config.daemonType = config.daemonType || 'default';
if (config.daemonType === 'bytecoin') {
	previousOffset = config.previousOffset || 3;
	offset = config.offset || 3;
}

function Create2DArray (rows) {
	let arr = [];
	for (let i = 0; i < rows; i++) {
		arr[i] = [];
	}
	return arr;
}

if (mergedMining) {
	config.childPools = config.childPools.filter(pool => pool.enabled);
}


// Block templates
let validBlockTemplates = mergedMining ? Create2DArray(config.childPools.length) : Create2DArray(1);
let currentBlockTemplate = [];


// Child Block templates
let currentChildBlockTemplate = new Array(mergedMining ? config.childPools.length : 1);


// Difficulty buffer
let diff1 = bignum('FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF', 16);

/**
 * Convert buffer to byte array
 **/
Buffer.prototype.toByteArray = function () {
	return Array.prototype.slice.call(this, 0);
};

/**
 * Periodical updaters
 **/

// Variable difficulty retarget
setInterval(function () {
	let now = Date.now() / 1000 | 0;
	for (let connID in connectedMiners) {
		let miner = connectedMiners[connID];
		if (!miner.noRetarget) {
			miner.retarget(now);
		}
	}
}, config.poolServer.varDiff.retargetTime * 1000);

// Every 30 seconds clear out timed-out miners and old bans
setInterval(function () {
	let now = Date.now();
	let timeout = config.poolServer.minerTimeout * 1000;
	for (let connID in connectedMiners) {
		let miner = connectedMiners[connID];
		if (now - miner.lastBeat > timeout) {
			log('warn', logSystem, 'Miner timed out and disconnected %s@%s', [miner.login, miner.ip]);
			delete connectedMiners[connID];
			removeConnectedWorker(miner, 'timeout');
		}
	}

	if (banningEnabled) {
		for (ip in bannedIPs) {
			let banTime = bannedIPs[ip];
			if (now - banTime > config.poolServer.banning.time * 1000) {
				delete bannedIPs[ip];
				delete perIPStats[ip];
				log('info', logSystem, 'Ban dropped for %s', [ip]);
			}
		}
	}

}, 30000);

/**
 * Handle multi-thread messages
 **/
process.on('message', function (message) {
	switch (message.type) {
		case 'banIP':
			bannedIPs[message.ip] = Date.now();
			break;
		case 'BlockTemplate':
                        newBlockTemplate(message.block);
                        break;
		case 'ChildBlockTemplate':
			let poolIndex = parseInt(message.poolIndex);
			try {
				if (!currentChildBlockTemplate[poolIndex] || message.block.height > currentChildBlockTemplate[poolIndex].height || (currentChildBlockTemplate[poolIndex].num_transactions == 0 && message.block.num_transactions > 0)) {
					log('info', logSystem, 'New %s child block to mine at height %d w/ difficulty of %d (%d transactions)', [config.childPools[poolIndex].coin, message.block.height, message.block.difficulty, (message.block.num_transactions || 0)]);
					processChildBlockTemplate(poolIndex, message.block);
					return;
				} else {
					return;
				}
			} catch (e) {
				log('error', logSystem, `ChildBlockTemplate ${e}`);
			}

			break;
	}
});

function newBlockTemplate(template) {
    let buffer = new Buffer(template.blocktemplate_blob, 'hex');
    let previous_hash = new Buffer(32);
    buffer.copy(previous_hash, 0, 9, 41);
    console.log('New block to mine at height: ' + template.height + '.  Difficulty: ' + template.difficulty);
    currentBlockTemplate = new BlockTemplate(template);
    for (let connID in connectedMiners) {
        if (currentMiners.hasOwnProperty(connID)) {
            let miner = connectedMiners[connID];
            debug(threadName + "Updating worker " + miner.payout + " With new work at height: " + template.height);
            miner.sendNewJob();
        }
    }
}

/**
 * Process block template
 **/
function processBlockTemplate (template, indexOfChildPool) {
	let block_template = new BlockTemplate(template, true, indexOfChildPool);

	if (currentBlockTemplate[indexOfChildPool]) {
		validBlockTemplates[indexOfChildPool].push(currentBlockTemplate[indexOfChildPool]);
	}

	while (validBlockTemplates[indexOfChildPool].length > (mergedMining ? 6 : 3)) {
		validBlockTemplates[indexOfChildPool].shift();
	}

	currentBlockTemplate[indexOfChildPool] = block_template;
	notifyConnectedMiners(indexOfChildPool);
}



/**
 * Process child block template
 **/
function processChildBlockTemplate (indexOfChildPool, template) {
	let block_template = new BlockTemplate(template, false);

	currentChildBlockTemplate[indexOfChildPool] = block_template;

	// Update the parent block template to include this new child
	if (currentBlockTemplate[indexOfChildPool]) {
		processBlockTemplate(currentBlockTemplate[indexOfChildPool], indexOfChildPool);
	}
}

function notifyConnectedMiners (indexOfChildPool) {
	let now = Date.now() / 1000 | 0;
	for (let connID in connectedMiners) {
		let miner = connectedMiners[connID];
		if (indexOfChildPool === miner.activeChildPool)
			miner.pushMessage('job', miner.getJob());
	}
}

/**
 * Variable difficulty
 **/
let VarDiff = (function () {
	let variance = config.poolServer.varDiff.variancePercent / 100 * config.poolServer.varDiff.targetTime;
	return {
		variance: variance,
		bufferSize: config.poolServer.varDiff.retargetTime / config.poolServer.varDiff.targetTime * 4,
		tMin: config.poolServer.varDiff.targetTime - variance,
		tMax: config.poolServer.varDiff.targetTime + variance,
		maxJump: config.poolServer.varDiff.maxJump
	};
})();

function GetRewardTypeAsKey (rewardType) {
	switch (rewardType) {
		case 'solo':
			return ':solo'
		case 'prop':
			return ''
		default:
			return ''
	}
}

/**
 * Miner
 **/
function Miner (rewardType, childRewardType, id, childPoolIndex, login, pass, ip, port, agent, childLogin, startingDiff, noRetarget, pushMessage) {
	this.rewardType = rewardType;
	this.childRewardType = childRewardType;
	this.rewardTypeAsKey = GetRewardTypeAsKey(rewardType);
	this.childRewardTypeAsKey = GetRewardTypeAsKey(childRewardType);

	this.lastChildBlockHeight = 0;
	this.id = id;
	this.activeChildPool = childPoolIndex || 0;
	this.login = login;
	this.pass = 'x';
	this.ip = ip;
	this.port = port;
	this.proxy = false;
	this.workerName = 'undefined';
	this.childLogin = childLogin;
	this.pushMessage = pushMessage;
	this.heartbeat();
	this.noRetarget = noRetarget;
	this.difficulty = startingDiff;
	this.validJobs = [];
	this.workerName2 = pass;

	// Vardiff related variables
	this.shareTimeRing = utils.ringBuffer(16);
	this.lastShareTime = Date.now() / 1000 | 0;

	if (shareTrustEnabled) {
		this.trust = {
			threshold: config.poolServer.shareTrust.threshold,
			probability: 1,
			penalty: 0
		};
	}
}
Miner.prototype = {
	retarget: function (now) {

		let options = config.poolServer.varDiff;
		let sinceLast = now - this.lastShareTime;
		let decreaser = sinceLast > VarDiff.tMax;
		let avg = this.shareTimeRing.avg(decreaser ? sinceLast : null);
		let newDiff;
		let direction;

		if (avg > VarDiff.tMax && this.difficulty > options.minDiff) {
			newDiff = options.targetTime / avg * this.difficulty;
			newDiff = newDiff > options.minDiff ? newDiff : options.minDiff;
			direction = -1;
		} else if (avg < VarDiff.tMin && this.difficulty < options.maxDiff) {
			newDiff = options.targetTime / avg * this.difficulty;
			newDiff = newDiff < options.maxDiff ? newDiff : options.maxDiff;
			direction = 1;
		} else {
			return;
		}
		if (Math.abs(newDiff - this.difficulty) / this.difficulty * 100 > options.maxJump) {
			let change = options.maxJump / 100 * this.difficulty * direction;
			newDiff = this.difficulty + change;
		}
		this.setNewDiff(newDiff);
		this.shareTimeRing.clear();
		if (decreaser) this.lastShareTime = now;
	},
	setNewDiff: function (newDiff) {
		newDiff = Math.round(newDiff);
		if (this.difficulty === newDiff) { 
			return; 
		}
		log('info', logSystem, 'Retargetting difficulty %d to %d for %s', [this.difficulty, newDiff, this.login]);
		this.pendingDifficulty = newDiff;
		this.pushMessage('job', this.getJob());
	},
	heartbeat: function () {
		this.lastBeat = Date.now();
	},
	getTargetHex: function () {
		if (this.pendingDifficulty) {
			this.lastDifficulty = this.difficulty;
			this.difficulty = this.pendingDifficulty;
			this.pendingDifficulty = null;
		}
		let padded = Buffer.alloc(32);
		padded.fill(0);
		let diffBuff = diff1.div(this.difficulty).toBuffer();
		diffBuff.copy(padded, 32 - diffBuff.length);
		let buff = padded.slice(0, 4);
		let buffArray = buff.toByteArray().reverse();
		let buffReversed = Buffer.from(buffArray);
		this.target = buffReversed.readUInt32BE(0);
		let hex = buffReversed.toString('hex');
		return hex;
	},
	getJob: function () {
		if (this.lastBlockHeight === currentBlockTemplate.height && currentBlockTemplate.idHash === this.validJobs.get(0).blockHash && !this.newDiff && this.cachedJob !== null) {
			return this.cachedJob;
		}

		if (!this.proxy) {
			let uniqueID = crypto.pseudoRandomBytes(8);

			let blob = currentBlockTemplate.nextBlob(uniqueID);
			let target = this.getTargetHex();
			this.lastBlockHeight = currentBlockTemplate.height;

			let newJob = {
				id: blob,
				unique_id: uniqueID,
				extraNonce: currentBlockTemplate.extraNonce,
				height: currentBlockTemplate.height,
				difficulty: this.difficulty,
				diffHex: this.diffHex,
				submissions: [],
				blockHash: currentBlockTemplate.idHash,
				seed: currentBlockTemplate.seed
			};

			this.validJobs.enq(newJob);
			let heightBuffer = Buffer.alloc(8);
			heightBuffer.writeUInt32BE(currentBlockTemplate.height, 4);
			this.cachedJob = [
				blob,
				'0x'+ currentBlockTemplate.seed,
				'0x'+ target,
				'0x'+ heightBuffer.toString('hex'),
			];
		} else {
			let blob = currentBlockTemplate.nextBlobWithChildNonce();
			if (this.newDiff) {
				this.difficulty = this.newDiff;
				this.newDiff = null;
			}
			this.lastBlockHeight = currentBlockTemplate.height;

			let newJob = {
				id: blob,
				extraNonce: currentBlockTemplate.extraNonce,
				height: currentBlockTemplate.height,
				difficulty: this.difficulty,
				diffHex: this.diffHex,
				clientPoolLocation: currentBlockTemplate.clientPoolLocation,
				clientNonceLocation: currentBlockTemplate.clientNonceLocation,
				submissions: [],
				seed: currentBlockTemplate.seed
			};
			this.validJobs.enq(newJob);
			this.cachedJob = {
				blocktemplate_blob: blob,
				difficulty: currentBlockTemplate.difficulty,
				height: currentBlockTemplate.height,
				reserved_offset: currentBlockTemplate.reserveOffset,
				client_nonce_offset: currentBlockTemplate.clientNonceLocation,
				client_pool_offset: currentBlockTemplate.clientPoolLocation,
				target_diff: this.difficulty,
				target_diff_hex: this.diffHex,
				job_id: newJob.id,
				id: this.id,
				seed: currentBlockTemplate.seed
			};
		}
		return this.cachedJob;
	},
	checkBan: function (validShare) {
		if (!banningEnabled) return;
		// Init global per-ip shares stats
		if (!perIPStats[this.ip]) {
			perIPStats[this.ip] = {
				validShares: 0,
				invalidShares: 0
			};
		}

		let stats = perIPStats[this.ip];
		validShare ? stats.validShares++ : stats.invalidShares++;

		if (stats.validShares + stats.invalidShares >= config.poolServer.banning.checkThreshold) {
			if (stats.invalidShares / stats.validShares >= config.poolServer.banning.invalidPercent / 100) {
				validShare ? this.validShares++ : this.invalidShares++;
				log('warn', logSystem, 'Banned %s@%s', [this.login, this.ip]);
				bannedIPs[this.ip] = Date.now();
				delete connectedMiners[this.id];
				process.send({
					type: 'banIP',
					ip: this.ip
				});
				removeConnectedWorker(this, 'banned');
			} else {
				stats.invalidShares = 0;
				stats.validShares = 0;
			}
		}
	}
};

validateMinerPaymentId_difficulty = (address, ip, poolServerConfig, coin, sendReply) => {
	if (utils.characterCount(address, '\\+') > 1) {
		let message = `Invalid paymentId specified for ${coin}login, ${ip}`;
		if (poolServerConfig.paymentId.validation) {
			process.send({
				type: 'banIP',
				ip: ip
			});
			message += ` banned for ${poolServerConfig.banning.time / 60} minutes`
		}
		sendReply(message);
		log('warn', logSystem, message);
		return false;
	}

	if (utils.characterCount(address, '\\.') > 1) {
		log('warn', logSystem, `Invalid difficulty specified for ${coin}login`);
		sendReply(`Invalid difficulty specified for ${coin}login, ${ip}`);
		return false;
	}
	return true;
}

/**
 * Handle miner method
 **/
function handleMinerMethod (method, params, ip, portData, sendReply, pushMessage, connID) {
	let miner = connectedMiners[connID];

	// Check for ban here, so preconnected attackers can't continue to screw you
	if (IsBannedIp(ip)) {
		sendReply('Your IP is banned');
		return;
	}

	switch (method) {
        case 'eth_submitLogin':
            if (params.length === 0 || !params[0]) {
                sendReply("No login specified");
                return;
            }

            let password = 'x';
            if (params.length > 1 && params[1]) {
                password = params[1];
            }

            difficulty = portData.difficulty;
            miner = new Miner(connID, params[0], password, ip, difficulty, pushMessage, 1, portData.portType, portData.port, '');
            if (!miner.valid_miner) {
                console.log("Invalid miner, disconnecting due to: " + miner.error);
                sendReply(miner.error);
                return;
            }
            process.send({type: 'newMiner', data: miner.port});
            connectedMiners[connID] = miner;
            sendReply(null, true);
            break;
        case 'eth_getWork':
            if (!miner) {
                miner = connectedMiners[connID];
            }
            if (!miner) {
                sendReply('Unauthenticated');
                return;
            }
            miner.heartbeat();
            miner.sendNewJob();
            break;
        case 'eth_submitWork':
            if (!miner) {
                sendReply('Unauthenticated');
                return;
            }

            if (params.length < 3 || !params[0] || !params[1] || !params[2]) {
                sendReply("No nonce/pow-hash/mix-digest specified");
                return;
            }

            miner.heartbeat();

            job = miner.validJobs.toarray().filter(function (job) {
                return job.id === params[1];
            })[0];

            if (!job) {
                sendReply('Invalid job id');
                console.warn(threadName + 'Invalid job: ' + JSON.stringify(params) + ' from ' + miner.logString);
                return;
            }

            if (!nonceCheck.test(params[0])) {
                console.warn(threadName + 'Malformed nonce: ' + JSON.stringify(params) + ' from ' + miner.logString);
                miner.checkBan(false);
                sendReply('Duplicate share');
                global.database.storeInvalidShare(miner.invalidShareProto);
                return;
            }

            if (job.submissions.indexOf(params[0]) !== -1) {
                console.warn(threadName + 'Duplicate share: ' + JSON.stringify(params) + ' from ' + miner.logString);
                miner.checkBan(false);
                sendReply('Duplicate share');
                global.database.storeInvalidShare(miner.invalidShareProto);
                return;
            }
            job.submissions.push(params[0]);


            blockTemplate = activeBlockTemplate.height === job.height ? activeBlockTemplate : pastBlockTemplates.toarray().filter(function (t) {
                return t.height === job.height;
            })[0];

            if (!blockTemplate) {
                console.warn(threadName + 'Block expired, Height: ' + job.height + ' from ' + miner.logString);
                if (miner.incremented === false) {
                    miner.newDiff = miner.difficulty + 1;
                    miner.incremented = true;
                } else {
                    miner.newDiff = miner.difficulty - 1;
                    miner.incremented = false;
                }
                miner.sendNewJob();
                sendReply('Block expired');
                global.database.storeInvalidShare(miner.invalidShareProto);
                return;
            }

            shareAccepted = processShare(miner, job, blockTemplate, params, sendReply);
            miner.checkBan(shareAccepted);

            if (global.config.pool.trustedMiners) {
                if (shareAccepted) {
                    miner.trust.probability -= global.config.pool.trustChange;
                    if (miner.trust.probability < (global.config.pool.trustMin)) {
                        miner.trust.probability = global.config.pool.trustMin;
                    }
                    miner.trust.penalty--;
                    miner.trust.threshold--;
                }
                else {
                    console.log(threadName + "Share trust broken by " + miner.logString);
                    global.database.storeInvalidShare(miner.invalidShareProto);
                    miner.trust.probability = 256;
                    miner.trust.penalty = global.config.pool.trustPenalty;
                    miner.trust.threshold = global.config.pool.trustThreshold;
                }
            }

            if (!shareAccepted) {
                sendReply('Low difficulty share');
                return;
            }

            now = Date.now() / 1000 || 0;
            miner.shareTimeBuffer.enq(now - miner.lastShareTime);
            miner.lastShareTime = now;

            sendReply(null, {status: 'OK'});
            break;
		case 'keepalived':
			if (!miner) {
				sendReply('Unauthenticated');
				return;
			}
			miner.heartbeat();
			sendReply(null, {
				status: 'KEEPALIVED'
			});
			break;
		default:
			sendReply('Invalid method');
			let minerText = miner ? (' ' + miner.login + '@' + miner.ip) : '';
			log('warn', logSystem, 'Invalid method: %s (%j) from %s', [method, params, minerText]);
			break;
	}
}

/**
 * New connected worker
 **/
function newConnectedWorker (miner) {
	log('info', logSystem, 'Miner connected %s@%s on port', [miner.login, miner.ip, miner.port]);
	if (miner.workerName !== 'undefined') log('info', logSystem, 'Worker Name: %s', [miner.workerName]);
	if (miner.difficulty) log('info', logSystem, 'Miner difficulty fixed to %s', [miner.difficulty]);

	redisClient.sadd(`${config.coin}:workers_ip:${miner.login}`, miner.ip);
	redisClient.hincrby(`${config.coin}:ports:${miner.port}`, 'users', 1);

	redisClient.hincrby(`${config.coin}:active_connections${miner.rewardTypeAsKey}`, `${miner.login}~${miner.workerName}`, 1, function (error, connectedWorkers) {
		if (connectedWorkers === 1) {
			notifications.sendToMiner(miner.login, 'workerConnected', {
				'LOGIN': miner.login,
				'MINER': `${miner.login.substring(0,7)}...${miner.login.substring(miner.login.length-7)}`,
				'IP': miner.ip.replace('::ffff:', ''),
				'PORT': miner.port,
				'WORKER_NAME': miner.workerName !== 'undefined' ? miner.workerName : ''
			});
		}
	});
	if (config.poolServer.mergedMining) {
		redisClient.sadd(`${config.childPools[miner.activeChildPool].coin}:workers_ip:${miner.childLogin}`, miner.ip);
		redisClient.hincrby(`${config.childPools[miner.activeChildPool].coin}:ports:${miner.port}`, 'users', 1);

		redisClient.hincrby(`${config.childPools[miner.activeChildPool].coin}:active_connections${miner.childRewardTypeAsKey}`, `${miner.childLogin}~${miner.workerName}`, 1, function (error, connectedWorkers) {});


		let redisCommands = config.childPools.map(item => {
			return ['hdel', `${config.coin}:workers:${miner.login}`, `${item.coin}`, ]
		})
		redisClient.multi(redisCommands)
			.exec(function (error, replies) {
				if (error) {
					log('error', logSystem, 'Failed to clear childCoins from parent in redis %j \n %j', [err, redisCommands]);
				}
			})

		redisClient.hset(`${config.coin}:workers:${miner.login}`, `${config.childPools[miner.activeChildPool].coin}`, miner.childLogin);

		redisClient.hset(`${config.childPools[miner.activeChildPool].coin}:workers:${miner.childLogin}`, `${config.coin}`, miner.login);

	}
}

/**
 * Remove connected worker
 **/
function removeConnectedWorker (miner, reason) {
	redisClient.hincrby(`${config.coin}:ports:${miner.port}`, 'users', '-1');
	if (mergedMining) {
		redisClient.hincrby(`${config.childPools[miner.activeChildPool].coin}:ports:${miner.port}`, 'users', '-1');
		redisClient.hincrby(`${config.childPools[miner.activeChildPool].coin}:active_connections${miner.childRewardTypeAsKey}`, `${miner.childLogin}~${miner.workerName}`, 1, function (error, connectedWorkers) {});
	}

	redisClient.hincrby(`${config.coin}:active_connections${miner.rewardTypeAsKey}`, `${miner.login}~${miner.workerName}`, -1, function (error, connectedWorkers) {
		if (reason === 'banned') {
			notifications.sendToMiner(miner.login, 'workerBanned', {
				'LOGIN': miner.login,
				'MINER': `${miner.login.substring(0,7)}...${miner.login.substring(miner.login.length-7)}`,
				'IP': miner.ip.replace('::ffff:', ''),
				'PORT': miner.port,
				'WORKER_NAME': miner.workerName !== 'undefined' ? miner.workerName : ''
			});
		} else if (!connectedWorkers || connectedWorkers <= 0) {
			notifications.sendToMiner(miner.login, 'workerTimeout', {
				'LOGIN': miner.login,
				'MINER': `${miner.login.substring(0,7)}...${miner.login.substring(miner.login.length-7)}`,
				'IP': miner.ip.replace('::ffff:', ''),
				'PORT': miner.port,
				'WORKER_NAME': miner.workerName !== 'undefined' ? miner.workerName : '',
				'LAST_HASH': utils.dateFormat(new Date(miner.lastBeat), 'yyyy-mm-dd HH:MM:ss Z')
			});
		}
	});
}

/**
 * Return if IP has been banned
 **/
function IsBannedIp (ip) {
	if (!banningEnabled || !bannedIPs[ip]) return false;

	let bannedTime = bannedIPs[ip];
	let bannedTimeAgo = Date.now() - bannedTime;
	let timeLeft = config.poolServer.banning.time * 1000 - bannedTimeAgo;
	if (timeLeft > 0) {
		return true;
	} else {
		delete bannedIPs[ip];
		log('info', logSystem, 'Ban dropped for %s', [ip]);
		return false;
	}
}

function recordShareData (miner, job, shareDiff, blockCandidate, hashHex, shareType, blockTemplate, pool) {
	let dateNow = Date.now();
	let dateNowSeconds = dateNow / 1000 | 0;
	let coin = pool !== null ? pool.coin : config.coin;
	let login = pool !== null ? miner.childLogin : miner.login;
	let job_height = pool !== null ? job.childHeight : job.height;
	let workerName = miner.workerName;
	let rewardType = pool !== null ? miner.childRewardType : miner.rewardType;
	let updateScore;
	// Weighting older shares lower than newer ones to prevent pool hopping
	if (slushMiningEnabled) {
		// We need to do this via an eval script because we need fetching the last block time and
		// calculating the score to run in a single transaction (otherwise we could have a race
		// condition where a block gets discovered between the time we look up lastBlockFound and
		// insert the score, which would give the miner an erroneously huge proportion on the new block)
		updateScore = ['eval', `
            local age = (ARGV[3] - redis.call('hget', KEYS[2], 'lastBlockFound')) / 1000
            local score = string.format('%.17g', ARGV[2] * math.exp(age / ARGV[4]))
            redis.call('hincrbyfloat', KEYS[1], ARGV[1], score)
            return {score, tostring(age)}
            `,
			2 /*keys*/ , coin + ':scores:roundCurrent', coin + ':stats',
			/* args */
			login, job.difficulty, Date.now(), config.poolServer.slushMining.weight
		];
	} else {
		job.score = job.difficulty;
		updateScore = ['hincrbyfloat', `${coin}:scores:${rewardType}:roundCurrent`, login, job.score]
	}

	let redisCommands = [
		updateScore,
		['hincrby', `${coin}:shares_actual:${rewardType}:roundCurrent`, login, job.difficulty],
		['zadd', `${coin}:hashrate`, dateNowSeconds, [job.difficulty, login, dateNow, rewardType].join(':')],
		['hincrby', `${coin}:workers:${login}`, 'hashes', job.difficulty],
		['hset', `${coin}:workers:${login}`, 'lastShare', dateNowSeconds],
		['expire', `${coin}:workers:${login}`, (86400 * cleanupInterval)],
		['expire', `${coin}:payments:${login}`, (86400 * cleanupInterval)]
	];

	if (workerName) {
		redisCommands.push(['zadd', `${coin}:hashrate`, dateNowSeconds, [job.difficulty, login + '~' + workerName, dateNow, rewardType].join(':')]);
		redisCommands.push(['hincrby', `${coin}:unique_workers:${login}~${workerName}`, 'hashes', job.difficulty]);
		redisCommands.push(['hset', `${coin}:unique_workers:${login}~${workerName}`, 'lastShare', dateNowSeconds]);
		redisCommands.push(['expire', `${coin}:unique_workers:${login}~${workerName}`, (86400 * cleanupInterval)]);
	}

	if (blockCandidate) {
		redisCommands.push(['hset', `${coin}:stats`, `lastBlockFound${rewardType}`, Date.now()]);
		redisCommands.push(['rename', `${coin}:scores:prop:roundCurrent`, coin + ':scores:prop:round' + job_height]);
		redisCommands.push(['rename', `${coin}:scores:solo:roundCurrent`, coin + ':scores:solo:round' + job_height]);
		redisCommands.push(['rename', `${coin}:shares_actual:prop:roundCurrent`, `${coin}:shares_actual:prop:round${job_height}`]);
		redisCommands.push(['rename', `${coin}:shares_actual:solo:roundCurrent`, `${coin}:shares_actual:solo:round${job_height}`]);
		if (rewardType === 'prop') {
			redisCommands.push(['hgetall', `${coin}:scores:prop:round${job_height}`]);
			redisCommands.push(['hgetall', `${coin}:shares_actual:prop:round${job_height}`]);
		}
		if (rewardType === 'solo') {
			redisCommands.push(['hget', `${coin}:scores:solo:round${job_height}`, login]);
			redisCommands.push(['hget', `${coin}:shares_actual:solo:round${job_height}`, login]);
		}

	}

	redisClient.multi(redisCommands)
		.exec(function (err, replies) {
			if (err) {
				log('error', logSystem, 'Failed to insert share data into redis %j \n %j', [err, redisCommands]);
				return;
			}

			if (slushMiningEnabled) {
				job.score = parseFloat(replies[0][0]);
				let age = parseFloat(replies[0][1]);
				log('info', logSystem, 'Submitted score ' + job.score + ' for difficulty ' + job.difficulty + ' and round age ' + age + 's');
			}

			if (blockCandidate) {
				let workerScores = replies[replies.length - 2];
				let workerShares = replies[replies.length - 1];
				let totalScore = 0;
				let totalShares = 0;
				if (rewardType === 'solo') {
					totalScore = workerScores
					totalShares = workerShares
				}
				if (rewardType === 'prop') {
					totalScore = Object.keys(workerScores)
						.reduce(function (p, c) {
							return p + parseFloat(workerScores[c])
						}, 0);
					totalShares = Object.keys(workerShares)
						.reduce(function (p, c) {
							return p + parseInt(workerShares[c])
						}, 0);
				}
				redisClient.zadd(coin + ':blocks:candidates', job_height, [
					rewardType,
					login,
					hashHex,
					Date.now() / 1000 | 0,
					blockTemplate.difficulty,
					totalShares,
					totalScore
				].join(':'), function (err, result) {
					if (err) {
						log('error', logSystem, 'Failed inserting block candidate %s \n %j', [hashHex, err]);
					}
				});

				notifications.sendToAll('blockFound', {
					'HEIGHT': job_height,
					'HASH': hashHex,
					'DIFFICULTY': blockTemplate.difficulty,
					'SHARES': totalShares,
					'MINER': login.substring(0, 7) + '...' + login.substring(login.length - 7)
				});
			}

		});

	log('info', logSystem, 'Accepted %s share at difficulty %d/%d from %s@%s', [shareType, job.difficulty, shareDiff, login, miner.ip]);
}

/**
 * Process miner share data
 **/
function processShare (miner, job, blockTemplate, params) {
    let nonce = params[0].substr(2);
    let resultHash = params[1].substr(2);

    let nonceBuffer = new Buffer(nonce, 'hex');
    let nonceBufferReversed = new Buffer(nonceBuffer.toByteArray().reverse());

    let hashBuffer = new Buffer(resultHash, 'hex');

    let heightBuffer = Buffer.alloc(8);
    heightBuffer.writeUInt32LE(job.height, 0);

    let shareBuffer = global.coinFuncs.getBlobFromBlockTemplate(blockTemplate.buffer, job.unique_id, nonceBufferReversed);

    let hash = global.coinFuncs.getPoWHash(hashBuffer, nonceBufferReversed, heightBuffer);
    let hashDiff = bignum.fromBuffer(hash);

    let blockTarget = baseDiff.div(bignum(blockTemplate.difficulty));
    let shareTarget = baseDiff.div(bignum(job.difficulty));

    let shareType = false;

    if (hashDiff.le(blockTarget)) {
        // Submit block to the RPC Daemon.
        // Todo: Implement within the coins/<coin>.js file.
        global.support.rpcDaemon('submitblock', [shareBuffer.toString('hex')], function (rpcResult) {
            if (rpcResult.error) {
                // Did not manage to submit a block.  Log and continue on.
                console.error(threadName + "Error submitting block at height " + job.height + " from " + miner.logString + ", share type: " + shareType + " error: " + JSON.stringify(rpcResult.error));
                recordShareData(miner, job, hashDiff.toString(), false, null, shareType);
                // Error on submit, so we'll submit a sanity check for good measure.
                templateUpdate();
            } else if (rpcResult) {
                //Success!  Submitted a block without an issue.
                let blockFastHash = global.coinFuncs.getBlockID(shareBuffer).toString('hex');
                console.log(threadName + "Block " + blockFastHash.substr(0, 6) + " found at height " + job.height + " by " + miner.logString +
                    ", share type: " + shareType + " - submit result: " + JSON.stringify(rpcResult.result));
                recordShareData(miner, job, hashDiff.toString(), true, blockFastHash, shareType, blockTemplate);
                templateUpdate();
            } else {
                // RPC bombed out massively.
                console.error(threadName + "RPC Error.  Please check logs for details");
            }
        });
    }
    else if (hashDiff.gt(shareTarget)) {
        process.send({type: 'invalidShare'});
        console.warn(threadName + "Rejected low diff share of " + hashDiff.toString() + " from: " + miner.address + " ID: " +
            miner.identifier + " IP: " + miner.ipAddress);
        return false;
    }
    else {
        recordShareData(miner, job, hashDiff.toString(), false, null, shareType);
    }
    return true;
}

/**
 * Start pool server on TCP ports
 **/
let httpResponse = ' 200 OK\nContent-Type: text/plain\nContent-Length: 20\n\nMining server online';

function startPoolServerTcp (callback) {
	log('info', logSystem, 'Clear values for connected workers in redis database.');
	redisClient.del(config.coin + ':active_connections');

	async.each(config.poolServer.ports, function (portData, cback) {
		let handleMessage = function (socket, jsonData, pushMessage, connID) {
			if (!jsonData.id) {
				log('warn', logSystem, 'Miner RPC request missing RPC id');
				return;
			} else if (!jsonData.method) {
				log('warn', logSystem, 'Miner RPC request missing RPC method');
				return;
			} else if (!jsonData.params) {
				log('warn', logSystem, 'Miner RPC request missing RPC params');
				return;
			}

			let sendReply = function (error, result) {
				if (!socket.writable) return;
				let sendData = JSON.stringify({
					id: jsonData.id,
					jsonrpc: "2.0",
					error: error ? {
						code: -1,
						message: error
					} : null,
					result: result
				}) + "\n";
				socket.write(sendData);
			};

			handleMinerMethod(jsonData.method, jsonData.params, socket.remoteAddress, portData, sendReply, pushMessage, connID);
		};

		let socketResponder = function (socket) {
			socket.setKeepAlive(true);
			socket.setEncoding('utf8');

			let dataBuffer = '';
            let connID = crypto.pseudoRandomBytes(21).toString('base64');

			let pushMessage = function (method, params) {
				if (!socket.writable) return;
				let sendData = JSON.stringify({
					jsonrpc: "2.0",
					method: method,
					params: params
				}) + "\n";
				socket.write(sendData);
			};

			socket.on('data', function (d) {
					dataBuffer += d;
					if (Buffer.byteLength(dataBuffer, 'utf8') > 10240) { //10KB
						dataBuffer = null;
						log('warn', logSystem, 'Socket flooding detected and prevented from %s', [socket.remoteAddress]);
						socket.destroy();
						return;
					}
					if (dataBuffer.indexOf('\n') !== -1) {
						let messages = dataBuffer.split('\n');
						let incomplete = dataBuffer.slice(-1) === '\n' ? '' : messages.pop();
						for (let i = 0; i < messages.length; i++) {
							let message = messages[i];
							if (message.trim() === '') continue;
							let jsonData;
							try {
								jsonData = JSON.parse(message);
							} catch (e) {
								if (message.indexOf('GET /') === 0) {
									if (message.indexOf('HTTP/1.1') !== -1) {
										socket.end('HTTP/1.1' + httpResponse);
										break;
									} else if (message.indexOf('HTTP/1.0') !== -1) {
										socket.end('HTTP/1.0' + httpResponse);
										break;
									}
								}

								log('warn', logSystem, 'Malformed message from %s: %s', [socket.remoteAddress, message]);
								socket.destroy();

								break;
							}
							try {
								handleMessage(socket, jsonData, pushMessage, connID);
							} catch (e) {
								log('warn', logSystem, 'Malformed message from ' + socket.remoteAddress + ' generated an exception. Message: ' + message);
								if (e.message) log('warn', logSystem, 'Exception: ' + e.message);
							}
						}
						dataBuffer = incomplete;
					}
				})
				.on('error', function (err) {
					if (err.code !== 'ECONNRESET')
						log('warn', logSystem, 'Socket error from %s %j', [socket.remoteAddress, err]);
				})
				.on('close', function () {
					pushMessage = function () {};
				});
		};

		if (portData.ssl) {
			if (!config.poolServer.sslCert) {
				log('error', logSystem, 'Could not start server listening on port %d (SSL): SSL certificate not configured', [portData.port]);
				cback(true);
			} else if (!config.poolServer.sslKey) {
				log('error', logSystem, 'Could not start server listening on port %d (SSL): SSL key not configured', [portData.port]);
				cback(true);
			} else if (!fs.existsSync(config.poolServer.sslCert)) {
				log('error', logSystem, 'Could not start server listening on port %d (SSL): SSL certificate file not found (configuration error)', [portData.port]);
				cback(true);
			} else if (!fs.existsSync(config.poolServer.sslKey)) {
				log('error', logSystem, 'Could not start server listening on port %d (SSL): SSL key file not found (configuration error)', [portData.port]);
				cback(true);
			} else {
				let options = {
					key: fs.readFileSync(config.poolServer.sslKey),
					cert: fs.readFileSync(config.poolServer.sslCert),
				};

				if (config.poolServer.sslCA && fs.existsSync(config.poolServer.sslCA)) {
					options.ca = fs.readFileSync(config.poolServer.sslCA)
				}

				tls.createServer(options, socketResponder)
					.listen(portData.port, function (error, result) {
						if (error) {
							log('error', logSystem, 'Could not start server listening on port %d (SSL), error: $j', [portData.port, error]);
							cback(true);
							return;
						}

						log('info', logSystem, 'Clear values for SSL port %d in redis database.', [portData.port]);
						redisClient.del(config.coin + ':ports:' + portData.port);
						redisClient.hset(config.coin + ':ports:' + portData.port, 'port', portData.port);

						log('info', logSystem, 'Started server listening on port %d (SSL)', [portData.port]);
						cback();
					});
			}
		} else {
			net.createServer(socketResponder)
				.listen(portData.port, function (error, result) {
					if (error) {
						log('error', logSystem, 'Could not start server listening on port %d, error: $j', [portData.port, error]);
						cback(true);
						return;
					}

					log('info', logSystem, 'Clear values for port %d in redis database.', [portData.port]);
					redisClient.del(config.coin + ':ports:' + portData.port);
					redisClient.hset(config.coin + ':ports:' + portData.port, 'port', portData.port);

					log('info', logSystem, 'Started server listening on port %d', [portData.port]);
					cback();
				});
		}
	}, function (err) {
		if (err) {
			callback(false);
		} else {
			callback(true);
		}
	});
}

/**
 * Initialize pool server
 **/

(function init (loop) {
	async.waterfall([
			function (callback) {
				if (!poolStarted) {
					startPoolServerTcp(function (successful) {
						poolStarted = true
					});
					setTimeout(init, 1000, loop);
					return;
				}
				callback(true)
			}
		],
		function (err) {
			if (loop === true) {
				setTimeout(function () {
					init(true);
				}, config.poolServer.blockRefreshInterval);
			}
		}
	);
})();
