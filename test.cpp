#include "SECP256k1.h"
#include "Base58.h"
#include "hash/sha256.h"
#include "hash/ripemd160.h"
#include <iostream>
#include <iomanip>
#include <sstream>
#include <cstring>

std::string BytesToHexString(const unsigned char *data, int len)
{
    std::stringstream ss;
    ss << std::hex;
    for (int i = 0; i < len; ++i)
        ss << std::setw(2) << std::setfill('0') << static_cast<int>(data[i]);
    return ss.str();
}

std::string GetBitcoinAddress(const Point &pubKey)
{
    unsigned char publicKey[33];
    unsigned char hash[32];
    unsigned char ripemd160[20];
    unsigned char address[25];

    // Compress public key
    publicKey[0] = pubKey.y.IsEven() ? 0x02 : 0x03;
    pubKey.x.Get32Bytes(publicKey + 1);

    // Perform SHA-256 hashing on the public key
    sha256_33(publicKey, hash);

    // Perform RIPEMD-160 hashing on the result of SHA-256
    ripemd160_32(hash, ripemd160);

    // Version byte + RIPEMD-160 hash
    address[0] = 0x00;
    std::memcpy(address + 1, ripemd160, 20);

    // Checksum
    sha256(address, 21, hash);
    sha256(hash, 32, hash);
    std::memcpy(address + 21, hash, 4);

    // Base58 encode
    return EncodeBase58(address, address + 25);
}

int main()
{
    Secp256K1 secp;
    secp.Init();

    std::string privKeyHex;
    std::cout << "Enter private key in hex format: ";
    std::cin >> privKeyHex;

    // Convert hex string to Int
    Int privKey;
    privKey.SetBase16(privKeyHex.c_str());

    // Compute public key
    Point pubKey = secp.ComputePublicKey(&privKey);

    // Get compressed public key
    unsigned char compressedPubKey[33];
    compressedPubKey[0] = pubKey.y.IsEven() ? 0x02 : 0x03;
    pubKey.x.Get32Bytes(compressedPubKey + 1);

    // Generate Bitcoin address
    std::string address = GetBitcoinAddress(pubKey);

    // Output results
    std::cout << "Private Key: " << privKeyHex << std::endl;
    std::cout << "Public Key (compressed): " << BytesToHexString(compressedPubKey, 33) << std::endl;
    std::cout << "Bitcoin Address: " << address << std::endl;

    return 0;
}