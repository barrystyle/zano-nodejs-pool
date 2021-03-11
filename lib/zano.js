"use strict";
const bignum = require('bignum');
const crypto = require('crypto');
const zanoUtil = require('cryptoforknote-util');

function Coin(data){

    this.data = data;
    this.coinDevAddress = "";  // Developer Address
    this.poolDevAddress = "";  // Snipa Address

    this.blockedAddresses = [
        this.coinDevAddress,
        this.poolDevAddress,
    ];

    this.exchangeAddresses = [
    ]; // These are addresses that MUST have a paymentID to perform logins with.

    this.prefix = 197;
    this.intPrefix = 0x3678;

    this.supportsAutoExchange = false;

    this.niceHashDiff = 400000;

    this.getBlockHeaderByID = function(blockId, callback){
        global.support.rpcDaemon('getblockheaderbyheight', {"height": blockId}, function (body) {
            if (body.hasOwnProperty('result')){
                return callback(null, body.result.block_header);
            } else {
                console.error(JSON.stringify(body));
                return callback(true, body);
            }
        });
    };

    this.getBlockHeaderByHash = function(blockHash, callback){
        global.support.rpcDaemon('getblockheaderbyhash', {"hash": blockHash}, function (body) {
            if (typeof(body) !== 'undefined' && body.hasOwnProperty('result')){
                return callback(null, body.result.block_header);
            } else {
                console.error(JSON.stringify(body));
                return callback(true, body);
            }
        });
    };

    this.getLastBlockHeader = function(callback){
        global.support.rpcDaemon('getlastblockheader', [], function (body) {
            if (typeof(body) !== 'undefined' && body.hasOwnProperty('result')){
                return callback(null, body.result.block_header);
            } else {
                console.error(JSON.stringify(body));
                return callback(true, body);
            }
        });
    };

    this.getBlockTemplate = function(walletAddress, callback){
        global.support.rpcDaemon('getblocktemplate', {
            reserve_size: 9,
            wallet_address: walletAddress
        }, function(body){
            return callback(body);
        });
    };

    this.baseDiff = function(){
        return bignum('FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF', 16);
    };

    this.validateAddress = function(address){
        // This function should be able to be called from the async library, as we need to BLOCK ever so slightly to verify the address.
        address = new Buffer(address);
        return zanoUtil.is_address_valid(address);
    };

    this.convertBlob = function(blobBuffer){
        return zanoUtil.convert_blob(blobBuffer);
    };

    this.getBlockID = function(blockBuffer){
        return zanoUtil.get_id_hash(blockBuffer);
    };

    this.getPoWHash = function(convertedBlob, nonce, height) {
        return zanoUtil.get_pow_hash(convertedBlob, nonce, height);
    };

    this.getHashFromBlockTemplateWithExtra = function(blockTemplate, extraData) {
        return zanoUtil.get_hash_from_block_template_with_extra(blockTemplate, extraData);
    };

    this.getBlobFromBlockTemplate = function(blockTemplate, extraData, nonce) {
        return zanoUtil.get_blob_from_block_template(blockTemplate, extraData, nonce);
    };

    this.BlockTemplate = function(template) {
        /*
        Generating a block template is a simple thing.  Ask for a boatload of information, and go from there.
        Important things to consider.
        The reserved space is 13 bytes long now in the following format:
        Assuming that the extraNonce starts at byte 130:
        |130-133|134-137|138-141|142-145|
        |minerNonce/extraNonce - 4 bytes|instanceId - 4 bytes|clientPoolNonce - 4 bytes|clientNonce - 4 bytes|
        This is designed to allow a single block template to be used on up to 4 billion poolSlaves (clientPoolNonce)
        Each with 4 billion clients. (clientNonce)
        While being unique to this particular pool thread (instanceId)
        With up to 4 billion clients (minerNonce/extraNonce)
        Overkill?  Sure.  But that's what we do here.  Overkill.
         */

        // Set this.blob equal to the BT blob that we get from upstream.
        this.blob = template.blocktemplate_blob;
        this.idHash = crypto.createHash('md5').update(template.blocktemplate_blob).digest('hex');
        // Set this.diff equal to the known diff for this block.
        this.difficulty = template.difficulty;
        // Set this.height equal to the known height for this block.
        this.height = template.height;
        // Set this.seed equal to the seed hash.
        this.seed = template.seed;
        // Set this.reserveOffset to the byte location of the reserved offset.
        this.reserveOffset = template.reserved_offset;
        // Set this.buffer to the binary decoded version of the BT blob.
        this.buffer = new Buffer(this.blob, 'hex');
        // Generate a clean, shiny new buffer.
        this.previous_hash = Buffer.alloc(32);
        // Copy in bytes 9 through 41 to this.previous_hash from the current BT.
        this.buffer.copy(this.previous_hash, 0, 9, 41);
        // Reset the Nonce. - This is the per-miner/pool nonce
        this.extraNonce = 0;
        // The clientNonceLocation is the location at which the client pools should set the nonces for each of their clients.
        this.clientNonceLocation = this.reserveOffset + 12;
        // The clientPoolLocation is for multi-thread/multi-server pools to handle the nonce for each of their tiers.
        this.clientPoolLocation = this.reserveOffset + 8;
        this.nextBlob = function (id) {
            // Convert the blob into something hashable.
            return '0x' + global.coinFuncs.getHashFromBlockTemplateWithExtra(this.buffer, id).toString('hex');
        };
        // Make it so you can get the raw block blob out.
        this.nextBlobWithChildNonce = function () {
            // Write a 32 bit integer, big-endian style to the 0 byte of the reserve offset.
            //this.buffer.writeUInt32BE(++this.extraNonce, this.reserveOffset);
            // Don't convert the blob to something hashable.  You bad.
            return this.buffer.toString('hex');
        };
    };
}

module.exports = Coin;

