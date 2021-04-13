/**
 * Cryptonote Node.JS Pool
 * https://github.com/dvandal/cryptonote-nodejs-pool
 *
 * Pool TCP daemon
 **/

// Load required modules
let debug = require('debug')('pool');
let fs = require('fs');
let crypto = require('crypto');
let net = require('net');
let tls = require('tls');
let async = require('async');
let bignum = require('bignum');
let baseDiff = global.coinFuncs.baseDiff();
let pastBlockTemplates = global.support.circularBuffer(4);
require('./apiInterfaces.js')(global.config.daemon, global.config.wallet, global.config.api);
let notifications = require('./notifications.js');
let utils = require('./utils.js');

// Set nonce pattern - must exactly be 8 hex chars
let nonceCheck = new RegExp("^0x[0-9a-f]{16}$");

// Set redis database cleanup interval
let cleanupInterval = global.config.redis.cleanupInterval && global.config.redis.cleanupInterval > 0 ? global.config.redis.cleanupInterval : 15;

// Initialize log system
let logSystem = 'pool';
require('./exceptionWriter.js')(logSystem);

let threadId = '(Thread ' + process.env.forkId + ') ';
let log = function (severity, system, text, data) {
    global.log(severity, system, threadId + text, data);
};

// Set cryptonight algorithm
let BlockTemplate = global.coinFuncs.BlockTemplate;
let currentBlockTemplate = [];

// Pool variables
let poolStarted = false;
let connectedMiners = {};

// Pool settings
let banningEnabled = global.config.poolServer.banning && global.config.poolServer.banning.enabled;
let bannedIPs = {};
let perIPStats = {};

let slushMiningEnabled = global.config.poolServer.slushMining && global.config.poolServer.slushMining.enabled;

if (!global.config.poolServer.paymentId) {
    global.config.poolServer.paymentId = {};
}
if (!global.config.poolServer.paymentId.addressSeparator) {
    global.config.poolServer.paymentId.addressSeparator = "+";
}

if (global.config.poolServer.paymentId.validation == null) {
    global.config.poolServer.paymentId.validation = true;
}
if (global.config.poolServer.paymentId.ban == null) {
    global.config.poolServer.paymentId.ban = false;
}
if (global.config.poolServer.paymentId.validations == null) {
    global.config.poolServer.paymentId.validations = [];
    global.config.poolServer.paymentId.validation = false;
}

let previousOffset = global.config.previousOffset || 7;
let offset = global.config.offset || 2;
global.config.daemonType = global.config.daemonType || 'default';

/**
 * Convert buffer to byte array
 **/
Buffer.prototype.toByteArray = function () {
    return Array.prototype.slice.call(this, 0);
};

/**
 * Periodical updaters
 **/

// Every 30 seconds clear out timed-out miners and old bans
setInterval(function () {
    let now = Date.now();
    let timeout = global.config.poolServer.minerTimeout * 1000;
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
            if (now - banTime > global.config.poolServer.banning.time * 1000) {
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
    }
});

function newBlockTemplate(template) {
    let buffer = new Buffer(template.blocktemplate_blob, 'hex');
    let previous_hash = Buffer.alloc(32);
    buffer.copy(previous_hash, 0, 9, 41);
    console.log('New block to mine at height: ' + template.height + '.  Difficulty: ' + template.difficulty);
    if (currentBlockTemplate) {
        pastBlockTemplates.enq(currentBlockTemplate);
    }
    currentBlockTemplate = new BlockTemplate(template);
    for (let connID in connectedMiners) {
         let miner = connectedMiners[connID];
         console.log('Updating worker ' + miner.payout + ' With new work at height: ' + template.height);
         miner.sinceLastJob = Date.now();
         miner.sharesSinceLastJob = 0;
         miner.sendNewJob();
    }
}

function GetRewardTypeAsKey(rewardType) {
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
function Miner(id, login, pass, ip, startingDiff, pushMessage, portType, port) {

    this.id = id;
    this.login = login;
    this.pass = 'x';
    this.ip = ip;
    this.port = port;
    this.proxy = false;
    this.valid_miner = true;
    this.workerName = 'undefined';
    this.pushMessage = pushMessage;
    this.heartbeat();
    this.difficulty = startingDiff;
    this.workerName2 = pass;

    // vardiff/performance tracking
    this.sinceLastJob = Date.now();
    this.sharesSinceLastJob = 0;
    this.sharesPerMinute = 0;

    this.validShares = 0;
    this.invalidShares = 0;
    this.hashes = 0;

    this.validJobs = global.support.circularBuffer(4);
    this.sentJobs = global.support.circularBuffer(8);
}

Miner.prototype = {
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
        let diffBuff = baseDiff.div(this.difficulty).toBuffer();
        diffBuff.copy(padded, 32 - diffBuff.length);
        let buff = padded.slice(0, 32);
        return buff.toString('hex');
    },
    getJob: function () {
        if (this.lastBlockHeight === currentBlockTemplate.height && currentBlockTemplate.idHash === this.validJobs.get(0).blockHash && !this.newDiff && this.cachedJob !== null) {
            return this.cachedJob;
        }

        {
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
                '0x' + currentBlockTemplate.seed,
                '0x' + target,
                '0x' + heightBuffer.toString('hex'),
            ];
            console.log(JSON.stringify(this.cachedJob, null, 4));
        }
        return this.cachedJob;
    },
    sendNewJob: function () {
        let job = this.getJob();
        let tempJob = this.sentJobs.toarray().filter(function (intJob) {
            return intJob.id === job[0];
        })[0];

        if (tempJob) {
            console.error(`Tried sending a duped job to: ${this.address}, stopped by Snipa!`);
            return;
        }
        this.sentJobs.enq(job);
        return this.job;
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

        if (stats.validShares + stats.invalidShares >= global.config.poolServer.banning.checkThreshold) {
            if (stats.invalidShares / stats.validShares >= global.config.poolServer.banning.invalidPercent / 100) {
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
function handleMinerMethod(method, params, ip, portData, sendReply, pushMessage, connID) {
    let miner = connectedMiners[connID];

    // Check for ban here, so preconnected attackers can't continue to screw you
    if (IsBannedIp(ip)) {
        sendReply('Your IP is banned');
        return;
    }

    switch (method)
    {
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
            miner = new Miner(connID, params[0], password, ip, difficulty, pushMessage, portData.portType, portData.port);
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
                if (!miner) {
                    sendReply('Unauthenticated');
                    return;
                }
            }
            miner.heartbeat();
            sendReply(miner.getJob());
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
                console.warn('Invalid job: ' + JSON.stringify(params) + ' from ' + miner.logString);
                return;
            }

            if (!nonceCheck.test(params[0])) {
                console.warn('Malformed nonce: ' + JSON.stringify(params) + ' from ' + miner.logString);
                miner.checkBan(false);
                sendReply('Duplicate share');
                global.database.storeInvalidShare(miner.invalidShareProto);
                return;
            }

            if (job.submissions.indexOf(params[0]) !== -1) {
                console.warn('Duplicate share: ' + JSON.stringify(params) + ' from ' + miner.logString);
                miner.checkBan(false);
                sendReply('Duplicate share');
                global.database.storeInvalidShare(miner.invalidShareProto);
                return;
            }
            job.submissions.push(params[0]);

            blockTemplate = currentBlockTemplate.height === job.height ? currentBlockTemplate : pastBlockTemplates.toarray().filter(function (t) {
                return t.height === job.height;
            })[0];

            if (!blockTemplate) {
                console.warn('Block expired, Height: ' + job.height + ' from ' + miner.logString);
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

            if (!shareAccepted) {
                sendReply('Low difficulty share');
                return;
            }

            // work out sharerate/spm
            miner.sharesSinceLastJob += 1;
            let timeSinceMs = Date.now() - miner.sinceLastJob;
            miner.sharesPerMinute = 0.5 * (miner.sharesPerMinute + (60000 / (timeSinceMs / miner.sharesSinceLastJob)));

            sendReply(true);
            break;
    }
}

/**
 * New connected worker
 **/
function newConnectedWorker(miner) {
    log('info', logSystem, 'Miner connected %s@%s on port', [miner.login, miner.ip, miner.port]);
    if (miner.workerName !== 'undefined') log('info', logSystem, 'Worker Name: %s', [miner.workerName]);
    if (miner.difficulty) log('info', logSystem, 'Miner difficulty fixed to %s', [miner.difficulty]);

    redisClient.sadd(`${global.config.coin}:workers_ip:${miner.login}`, miner.ip);
    redisClient.hincrby(`${global.config.coin}:ports:${miner.port}`, 'users', 1);

    redisClient.hincrby(`${global.config.coin}:active_connections${miner.rewardTypeAsKey}`, `${miner.login}~${miner.workerName}`, 1, function (error, connectedWorkers) {
        if (connectedWorkers === 1) {
            notifications.sendToMiner(miner.login, 'workerConnected', {
                'LOGIN': miner.login,
                'MINER': `${miner.login.substring(0, 7)}...${miner.login.substring(miner.login.length - 7)}`,
                'IP': miner.ip.replace('::ffff:', ''),
                'PORT': miner.port,
                'WORKER_NAME': miner.workerName !== 'undefined' ? miner.workerName : ''
            });
        }
    });
}

/**
 * Remove connected worker
 **/
function removeConnectedWorker(miner, reason) {
    redisClient.hincrby(`${global.config.coin}:ports:${miner.port}`, 'users', '-1');

    redisClient.hincrby(`${global.config.coin}:active_connections${miner.rewardTypeAsKey}`, `${miner.login}~${miner.workerName}`, -1, function (error, connectedWorkers) {
        if (reason === 'banned') {
            notifications.sendToMiner(miner.login, 'workerBanned', {
                'LOGIN': miner.login,
                'MINER': `${miner.login.substring(0, 7)}...${miner.login.substring(miner.login.length - 7)}`,
                'IP': miner.ip.replace('::ffff:', ''),
                'PORT': miner.port,
                'WORKER_NAME': miner.workerName !== 'undefined' ? miner.workerName : ''
            });
        } else if (!connectedWorkers || connectedWorkers <= 0) {
            notifications.sendToMiner(miner.login, 'workerTimeout', {
                'LOGIN': miner.login,
                'MINER': `${miner.login.substring(0, 7)}...${miner.login.substring(miner.login.length - 7)}`,
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
function IsBannedIp(ip) {
    if (!banningEnabled || !bannedIPs[ip]) return false;

    let bannedTime = bannedIPs[ip];
    let bannedTimeAgo = Date.now() - bannedTime;
    let timeLeft = global.config.poolServer.banning.time * 1000 - bannedTimeAgo;
    if (timeLeft > 0) {
        return true;
    } else {
        delete bannedIPs[ip];
        log('info', logSystem, 'Ban dropped for %s', [ip]);
        return false;
    }
}

function recordShareData(miner, job, shareDiff, blockCandidate, hashHex, blockTemplate, pool) {
    let dateNow = Date.now();
    let dateNowSeconds = dateNow / 1000 | 0;
    let coin = global.config.coin;
    let login = pool !== miner.login;
    let job_height = pool !== job.height;
    let workerName = miner.workerName;
    let rewardType = pool !== miner.rewardType;
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
            2 /*keys*/, coin + ':scores:roundCurrent', coin + ':stats',
            /* args */
            login, job.difficulty, Date.now(), global.config.poolServer.slushMining.weight
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

    log('info', logSystem, 'Accepted share at difficulty %d/%d from %s', [job.difficulty, baseDiff.div(bignum(shareDiff)), miner.login]);
}

/**
 * Process miner share data
 **/
function processShare(miner, job, blockTemplate, params, sendReply) {
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
                console.error("Error submitting block at height " + job.height + " from " + miner.logString + ", share type: " + shareType + " error: " + JSON.stringify(rpcResult.error));
                recordShareData(miner, job, hashDiff.toString(), false, null, shareType);
                // Error on submit, so we'll submit a sanity check for good measure.
                templateUpdate();
            } else if (rpcResult) {
                //Success!  Submitted a block without an issue.
                let blockFastHash = global.coinFuncs.getBlockID(shareBuffer).toString('hex');
                console.log("Block " + blockFastHash.substr(0, 6) + " found at height " + job.height + " by " + miner.logString +
                    ", share type: " + shareType + " - submit result: " + JSON.stringify(rpcResult.result));
                recordShareData(miner, job, hashDiff.toString(), true, blockFastHash, shareType, blockTemplate);
                templateUpdate();
            } else {
                // RPC bombed out massively.
                console.error("RPC Error.  Please check logs for details");
            }
        });
    } else if (hashDiff.gt(shareTarget)) {
        process.send({type: 'invalidShare'});
        console.warn("Rejected low diff share of " + hashDiff.toString() + " from: " + miner.address + " ID: " +
            miner.identifier + " IP: " + miner.ipAddress);
        return false;
    } else {
        recordShareData(miner, job, hashDiff.toString(), false, null, shareType);
    }
    return true;
}

/**
 * Start pool server on TCP ports
 **/
let httpResponse = ' 200 OK\nContent-Type: text/plain\nContent-Length: 20\n\nMining server online';

function startPoolServerTcp(callback) {
    log('info', logSystem, 'Clear values for connected workers in redis database.');
    redisClient.del(global.config.coin + ':active_connections');

    async.each(global.config.poolServer.ports, function (portData, cback) {
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

            let sendReply = function (message, result) {
                if (!socket.writable) return;
                let sendData = JSON.stringify({
                    id: jsonData.id,
                    jsonrpc: "2.0",
                    result: message
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

            let pushMessage = function (method, params, id) {
                if (!socket.writable) {
                    return;
                }
                let obj = {
                    jsonrpc: "2.0",
                    result: params
                };
                if (method) {
                    obj.method = method;
                }
                if (typeof id !== 'undefined') {
                    obj.id = id;
                }
                let sendData = JSON.stringify(obj) + "\n";

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
                    pushMessage = function () {
                    };
                });
        };

        if (portData.ssl) {
            if (!global.config.poolServer.sslCert) {
                log('error', logSystem, 'Could not start server listening on port %d (SSL): SSL certificate not configured', [portData.port]);
                cback(true);
            } else if (!global.config.poolServer.sslKey) {
                log('error', logSystem, 'Could not start server listening on port %d (SSL): SSL key not configured', [portData.port]);
                cback(true);
            } else if (!fs.existsSync(global.config.poolServer.sslCert)) {
                log('error', logSystem, 'Could not start server listening on port %d (SSL): SSL certificate file not found (configuration error)', [portData.port]);
                cback(true);
            } else if (!fs.existsSync(global.config.poolServer.sslKey)) {
                log('error', logSystem, 'Could not start server listening on port %d (SSL): SSL key file not found (configuration error)', [portData.port]);
                cback(true);
            } else {
                let options = {
                    key: fs.readFileSync(global.config.poolServer.sslKey),
                    cert: fs.readFileSync(global.config.poolServer.sslCert),
                };

                if (global.config.poolServer.sslCA && fs.existsSync(global.config.poolServer.sslCA)) {
                    options.ca = fs.readFileSync(global.config.poolServer.sslCA)
                }

                tls.createServer(options, socketResponder)
                    .listen(portData.port, function (error, result) {
                        if (error) {
                            log('error', logSystem, 'Could not start server listening on port %d (SSL), error: $j', [portData.port, error]);
                            cback(true);
                            return;
                        }

                        log('info', logSystem, 'Clear values for SSL port %d in redis database.', [portData.port]);
                        redisClient.del(global.config.coin + ':ports:' + portData.port);
                        redisClient.hset(global.config.coin + ':ports:' + portData.port, 'port', portData.port);

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
                    redisClient.del(global.config.coin + ':ports:' + portData.port);
                    redisClient.hset(global.config.coin + ':ports:' + portData.port, 'port', portData.port);

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

(function init(loop) {
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
                }, global.config.poolServer.blockRefreshInterval);
            }
        }
    );
})();
