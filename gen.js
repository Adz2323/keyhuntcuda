// Elliptic curve parameters for secp256k1
const P = BigInt("0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F");
const A = BigInt(0);
const B = BigInt(7);
const Gx = BigInt("0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798");
const Gy = BigInt("0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8");
const N = BigInt("0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141");

// Helper function to perform modular inversion
function modInverse(a, m) {
    let m0 = m, t, q;
    let x0 = 0n, x1 = 1n;
    if (m === 1n) return 0n;
    while (a > 1n) {
        q = a / m;
        t = m;
        m = a % m, a = t;
        t = x0;
        x0 = x1 - q * x0;
        x1 = t;
    }
    if (x1 < 0n) x1 += m0;
    return x1;
}

// Helper function to perform modular addition
function modAdd(a, b, m) {
    return (a + b) % m;
}

// Helper function to perform modular subtraction
function modSub(a, b, m) {
    return (a - b + m) % m;
}

// Helper function to perform modular multiplication
function modMul(a, b, m) {
    return (a * b) % m;
}

// Generate a random 256-bit private key
function generatePrivateKey() {
    let array = new Uint8Array(32);
    for (let i = 0; i < 32; i++) {
        array[i] = Math.floor(Math.random() * 256);
    }
    return BigInt('0x' + Array.from(array)
        .map(byte => byte.toString(16).padStart(2, '0')).join('')) % N;
}

// Perform point doubling on the elliptic curve
function pointDouble(x, y) {
    const m = modMul(3n * x * x, modInverse(2n * y, P), P);
    const xr = modSub(modMul(m, m, P), modMul(2n, x, P), P);
    const yr = modSub(modMul(m, modSub(x, xr, P), P), y, P);
    return [xr, yr];
}

// Perform point addition on the elliptic curve
function pointAdd(x1, y1, x2, y2) {
    if (x1 === x2 && y1 === y2) return pointDouble(x1, y1);
    const m = modMul(modSub(y2, y1, P), modInverse(modSub(x2, x1, P), P), P);
    const xr = modSub(modMul(m, m, P), x1, P);
    const yr = modSub(modMul(m, modSub(x1, xr, P), P), y1, P);
    return [xr, yr];
}

// Perform scalar multiplication on the elliptic curve
function scalarMultiply(k, x, y) {
    let currentX = x;
    let currentY = y;
    let resultX = 0n;
    let resultY = 0n;
    let addResult = false;

    while (k > 0n) {
        if (k & 1n) {
            if (!addResult) {
                resultX = currentX;
                resultY = currentY;
                addResult = true;
            } else {
                [resultX, resultY] = pointAdd(resultX, resultY, currentX, currentY);
            }
        }
        [currentX, currentY] = pointDouble(currentX, currentY);
        k >>= 1n;
    }

    return [resultX, resultY];
}

// SHA-256 implementation
function sha256(hex) {
    const message = new Uint8Array(hex.match(/.{1,2}/g).map(byte => parseInt(byte, 16)));

    function rightRotate(value, amount) {
        return (value >>> amount) | (value << (32 - amount));
    }

    const k = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
    ];

    const hash = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
        0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
    ];

    const originalByteLength = message.length;

    // Padding
    const bitLength = originalByteLength * 8;
    const paddingLength = (bitLength + 1 + 64) % 512;
    const totalLength = originalByteLength + 1 + paddingLength / 8 + 8;
    const paddedMessage = new Uint8Array(totalLength);
    paddedMessage.set(message);
    paddedMessage[originalByteLength] = 0x80;
    for (let i = 0; i < 8; i++) {
        paddedMessage[paddedMessage.length - 1 - i] = (bitLength >>> (8 * i)) & 0xff;
    }

    // Process the message in successive 512-bit chunks:
    for (let i = 0; i < paddedMessage.length / 64; i++) {
        const chunk = paddedMessage.slice(i * 64, (i + 1) * 64);
        const w = new Uint32Array(64);

        for (let j = 0; j < 16; j++) {
            w[j] = (chunk[j * 4] << 24) | (chunk[j * 4 + 1] << 16) | (chunk[j * 4 + 2] << 8) | chunk[j * 4 + 3];
        }

        for (let j = 16; j < 64; j++) {
            const s0 = rightRotate(w[j - 15], 7) ^ rightRotate(w[j - 15], 18) ^ (w[j - 15] >>> 3);
            const s1 = rightRotate(w[j - 2], 17) ^ rightRotate(w[j - 2], 19) ^ (w[j - 2] >>> 10);
            w[j] = (w[j - 16] + s0 + w[j - 7] + s1) >>> 0;
        }

        let [a, b, c, d, e, f, g, h] = hash;

        for (let j = 0; j < 64; j++) {
            const S1 = rightRotate(e, 6) ^ rightRotate(e, 11) ^ rightRotate(e, 25);
            const ch = (e & f) ^ (~e & g);
            const temp1 = (h + S1 + ch + k[j] + w[j]) >>> 0;
            const S0 = rightRotate(a, 2) ^ rightRotate(a, 13) ^ rightRotate(a, 22);
            const maj = (a & b) ^ (a & c) ^ (b & c);
            const temp2 = (S0 + maj) >>> 0;

            h = g;
            g = f;
            f = e;
            e = (d + temp1) >>> 0;
            d = c;
            c = b;
            b = a;
            a = (temp1 + temp2) >>> 0;
        }

        hash[0] = (hash[0] + a) >>> 0;
        hash[1] = (hash[1] + b) >>> 0;
        hash[2] = (hash[2] + c) >>> 0;
        hash[3] = (hash[3] + d) >>> 0;
        hash[4] = (hash[4] + e) >>> 0;
        hash[5] = (hash[5] + f) >>> 0;
        hash[6] = (hash[6] + g) >>> 0;
        hash[7] = (hash[7] + h) >>> 0;
    }

    return Array.from(new Uint8Array(new Uint32Array(hash).buffer))
        .map(byte => byte.toString(16).padStart(2, '0')).join('');
}

// RIPEMD-160 implementation (placeholder)
// RIPEMD-160 implementation
function ripemd160(message) {
    function f(j, x, y, z) {
        if (j < 16) return x ^ y ^ z;
        if (j < 32) return (x & y) | (~x & z);
        if (j < 48) return (x | ~y) ^ z;
        if (j < 64) return (x & z) | (y & ~z);
        return x ^ (y | ~z);
    }

    function K(j) {
        if (j < 16) return 0x00000000;
        if (j < 32) return 0x5a827999;
        if (j < 48) return 0x6ed9eba1;
        if (j < 64) return 0x8f1bbcdc;
        return 0xa953fd4e;
    }

    function KP(j) {
        if (j < 16) return 0x50a28be6;
        if (j < 32) return 0x5c4dd124;
        if (j < 48) return 0x6d703ef3;
        if (j < 64) return 0x7a6d76e9;
        return 0x00000000;
    }

    function rotateLeft(x, n) {
        return (x << n) | (x >>> (32 - n));
    }

    function padding(message) {
        const messageLength = message.length * 8;
        const paddingLength = (message.length % 64 < 56) ? (56 - (message.length % 64)) : (120 - (message.length % 64));
        const paddedMessage = new Uint8Array(message.length + paddingLength + 8);
        paddedMessage.set(message);
        paddedMessage[message.length] = 0x80;
        paddedMessage.set(new Uint8Array(new Uint32Array([messageLength]).buffer).reverse(), paddedMessage.length - 8);
        return paddedMessage;
    }

    function processBlock(H, block) {
        const r = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8,
            3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12, 1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2,
            4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13, 5, 14, 7, 0, 9, 2, 11, 4, 12, 6, 13, 15, 8, 1, 10, 3,
            6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2, 7, 2, 6, 13, 11, 8, 1, 4, 10, 15, 14, 3, 9, 12, 0, 5];
        const s = [11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8, 7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12,
            11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5, 11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12,
            9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6, 8, 6, 5, 12, 9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14];
        const H0 = H.slice(0);

        let A1 = H0[0], B1 = H0[1], C1 = H0[2], D1 = H0[3], E1 = H0[4];
        let A2 = H0[0], B2 = H0[1], C2 = H0[2], D2 = H0[3], E2 = H0[4];

        for (let j = 0; j < 80; j++) {
            const T = rotateLeft(A1 + f(j, B1, C1, D1) + block[r[j]] + K(j), s[j]) + E1;
            A1 = E1;
            E1 = D1;
            D1 = rotateLeft(C1, 10);
            C1 = B1;
            B1 = T;

            const T2 = rotateLeft(A2 + f(79 - j, B2, C2, D2) + block[r[j]] + KP(j), s[j]) + E2;
            A2 = E2;
            E2 = D2;
            D2 = rotateLeft(C2, 10);
            C2 = B2;
            B2 = T2;
        }

        const T = H0[1] + C1 + D2;
        H0[1] = H0[2] + D1 + E2;
        H0[2] = H0[3] + E1 + A2;
        H0[3] = H0[4] + A1 + B2;
        H0[4] = H0[0] + B1 + C2;
        H0[0] = T;

        return H0;
    }

    const paddedMessage = padding(new TextEncoder().encode(message));
    const H = [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0];

    for (let i = 0; i < paddedMessage.length; i += 64) {
        const block = new Uint32Array(paddedMessage.slice(i, i + 64).buffer);
        processBlock(H, block);
    }

    return H.map(h => h.toString(16).padStart(8, '0')).join('');
}

// Encode in Base58
function encodeBase58(hex) {
    const alphabet = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
    let num = BigInt('0x' + hex);
    let output = '';
    while (num > 0n) {
        const remainder = num % 58n;
        num = num / 58n;
        output = alphabet[remainder] + output;
    }
    return output;
}

// Generate Bitcoin address from public key
function generateBitcoinAddress(publicKeyX, publicKeyY) {
    const prefix = publicKeyY % 2n === 0n ? '02' : '03';
    const publicKey = prefix + publicKeyX.toString(16).padStart(64, '0');
    const hash160 = ripemd160(sha256(publicKey));
    const address = '00' + hash160;
    const checksum = sha256(sha256(address)).substring(0, 8);
    return encodeBase58(address + checksum);
}

// Main function to generate keys and address
function generateKeysAndAddress() {
    const privateKey = generatePrivateKey();
    console.log("Private Key: " + privateKey.toString(16).padStart(64, '0'));

    const [publicKeyX, publicKeyY] = scalarMultiply(privateKey, Gx, Gy);
    console.log("Public Key X: " + publicKeyX.toString(16).padStart(64, '0'));
    console.log("Public Key Y: " + publicKeyY.toString(16).padStart(64, '0'));

    const bitcoinAddress = generateBitcoinAddress(publicKeyX, publicKeyY);
    console.log("Bitcoin Address: " + bitcoinAddress);
}

generateKeysAndAddress();
