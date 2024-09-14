#include "KeyHunt.h"
#include "GmpUtil.h"
#include "Base58.h"
#include "hash/sha256.h"
#include "hash/keccak160.h"
#include "IntGroup.h"
#include "Timer.h"
#include "hash/ripemd160.h"
#include <cstring>
#include <cmath>
#include <algorithm>
#include <iostream>
#include <cassert>
#ifndef WIN64
#include <pthread.h>
#include <random>
#endif

// using namespace std;

Point Gn[CPU_GRP_SIZE / 2];
Point _2Gn;
std::random_device rd;
std::mt19937 gen(rd());
// ----------------------------------------------------------------------------

KeyHunt::KeyHunt(const std::string &inputFile, int compMode, int searchMode, int coinType, bool useGpu,
				 const std::string &outputFile, bool useSSE, uint32_t maxFound, uint64_t rKey,
				 const std::string &rangeStart, const std::string &rangeEnd, bool &should_exit, bool useSegment,
				 bool fullyRandom)
{
	this->compMode = compMode;
	this->useGpu = useGpu;
	this->outputFile = outputFile;
	this->useSSE = useSSE;
	this->nbGPUThread = 0;
	this->inputFile = inputFile;
	this->maxFound = maxFound;
	this->rKey = rKey;
	this->searchMode = searchMode;
	this->coinType = coinType;
	this->rangeStart.SetBase16(rangeStart.c_str());
	this->rangeEnd.SetBase16(rangeEnd.c_str());
	this->rangeDiff2.Set(&this->rangeEnd);
	this->rangeDiff2.Sub(&this->rangeStart);
	this->lastrKey = 0;
	this->useSegment = useSegment;
	this->debugMode = false;
	this->maxThreads = 0;
	this->rangeDiffs = nullptr;
	this->printDebug = false;
	this->debugUpdateInterval = 1000000;
	this->debugInterval = 1000000;
	this->fullyRandom = fullyRandom;

	secp = new Secp256K1();
	secp->Init();

	// load file
	FILE *wfd;
	uint64_t N = 0;

	wfd = fopen(this->inputFile.c_str(), "rb");
	if (!wfd)
	{
		printf("%s can not open\n", this->inputFile.c_str());
		exit(1);
	}

#ifdef WIN64
	_fseeki64(wfd, 0, SEEK_END);
	N = _ftelli64(wfd);
#else
	fseek(wfd, 0, SEEK_END);
	N = ftell(wfd);
#endif

	int K_LENGTH = 20;
	if (this->searchMode == (int)SEARCH_MODE_MX)
		K_LENGTH = 32;

	N = N / K_LENGTH;
	rewind(wfd);

	DATA = (uint8_t *)malloc(N * K_LENGTH);
	memset(DATA, 0, N * K_LENGTH);

	uint8_t *buf = (uint8_t *)malloc(K_LENGTH);
	;

	bloom = new Bloom(2 * N, 0.000001);

	uint64_t percent = (N - 1) / 100;
	uint64_t i = 0;
	printf("\n");
	while (i < N && !should_exit)
	{
		memset(buf, 0, K_LENGTH);
		memset(DATA + (i * K_LENGTH), 0, K_LENGTH);
		if (fread(buf, 1, K_LENGTH, wfd) == K_LENGTH)
		{
			bloom->add(buf, K_LENGTH);
			memcpy(DATA + (i * K_LENGTH), buf, K_LENGTH);
			if ((percent != 0) && i % percent == 0)
			{
				printf("\rLoading      : %llu %%", (i / percent));
				fflush(stdout);
			}
		}
		i++;
	}
	fclose(wfd);
	free(buf);

	if (should_exit)
	{
		delete secp;
		delete bloom;
		if (DATA)
			free(DATA);
		exit(0);
	}

	BLOOM_N = bloom->get_bytes();
	TOTAL_COUNT = N;
	targetCounter = i;
	if (coinType == COIN_BTC)
	{
		if (searchMode == (int)SEARCH_MODE_MA)
			printf("Loaded       : %s Bitcoin addresses\n", formatThousands(i).c_str());
		else if (searchMode == (int)SEARCH_MODE_MX)
			printf("Loaded       : %s Bitcoin xpoints\n", formatThousands(i).c_str());
	}
	else
	{
		printf("Loaded       : %s Ethereum addresses\n", formatThousands(i).c_str());
	}

	printf("\n");

	bloom->print();
	printf("\n");

	InitGenratorTable();
}

// ----------------------------------------------------------------------------

KeyHunt::KeyHunt(const std::vector<unsigned char> &hashORxpoint, int compMode, int searchMode, int coinType,
				 bool useGpu, const std::string &outputFile, bool useSSE, uint32_t maxFound, uint64_t rKey,
				 const std::string &rangeStart, const std::string &rangeEnd, bool &should_exit, bool useSegment,
				 bool fullyRandom)
{
	this->compMode = compMode;
	this->useGpu = useGpu;
	this->outputFile = outputFile;
	this->useSSE = useSSE;
	this->nbGPUThread = 0;
	this->maxFound = maxFound;
	this->rKey = rKey;
	this->searchMode = searchMode;
	this->coinType = coinType;
	this->rangeStart.SetBase16(rangeStart.c_str());
	this->rangeEnd.SetBase16(rangeEnd.c_str());
	this->rangeDiff2.Set(&this->rangeEnd);
	this->rangeDiff2.Sub(&this->rangeStart);
	this->targetCounter = 1;
	this->useSegment = useSegment;
	this->debugMode = false;
	this->maxThreads = 0;
	this->rangeDiffs = nullptr;
	this->printDebug = false;
	this->debugUpdateInterval = 1000000;
	this->debugInterval = 1000000;
	this->fullyRandom = fullyRandom;

	secp = new Secp256K1();
	secp->Init();

	if (this->searchMode == (int)SEARCH_MODE_SA)
	{
		assert(hashORxpoint.size() == 20);
		for (size_t i = 0; i < hashORxpoint.size(); i++)
		{
			((uint8_t *)hash160Keccak)[i] = hashORxpoint.at(i);
		}
	}
	else if (this->searchMode == (int)SEARCH_MODE_SX)
	{
		assert(hashORxpoint.size() == 32);
		for (size_t i = 0; i < hashORxpoint.size(); i++)
		{
			((uint8_t *)xpoint)[i] = hashORxpoint.at(i);
		}
	}
	printf("\n");

	InitGenratorTable();
}

// ----------------------------------------------------------------------------

void KeyHunt::InitGenratorTable()
{
	// Compute Generator table G[n] = (n+1)*G
	Point g = secp->G;
	Gn[0] = g;
	g = secp->DoubleDirect(g);
	Gn[1] = g;
	for (int i = 2; i < CPU_GRP_SIZE / 2; i++)
	{
		g = secp->AddDirect(g, secp->G);
		Gn[i] = g;
	}
	// _2Gn = CPU_GRP_SIZE*G
	_2Gn = secp->DoubleDirect(Gn[CPU_GRP_SIZE / 2 - 1]);

	char *ctimeBuff;
	time_t now = time(NULL);
	ctimeBuff = ctime(&now);
	printf("Start Time   : %s", ctimeBuff);

	if (rKey > 0)
	{
		printf("Base Key     : Randomly changes on every %lu Mkeys\n", rKey);
	}
	printf("Global start : %s (%d bit)\n", this->rangeStart.GetBase16().c_str(), this->rangeStart.GetBitLength());
	printf("Global end   : %s (%d bit)\n", this->rangeEnd.GetBase16().c_str(), this->rangeEnd.GetBitLength());
	printf("Global range : %s (%d bit)\n", this->rangeDiff2.GetBase16().c_str(), this->rangeDiff2.GetBitLength());
}

// ----------------------------------------------------------------------------

KeyHunt::~KeyHunt()
{
	delete secp;
	if (searchMode == (int)SEARCH_MODE_MA || searchMode == (int)SEARCH_MODE_MX)
		delete bloom;
	if (DATA)
		free(DATA);
}

// ----------------------------------------------------------------------------

// ----------------------------------------------------------------------------
void KeyHunt::GenerateBitcoinAddress(Point pubKey, bool compressed, std::string &address)
{
	unsigned char publicKeyBytes[65];
	unsigned char hash[32];
	unsigned char ripemd160_hash[20];
	unsigned char addressBytes[25];

	if (compressed)
	{
		publicKeyBytes[0] = pubKey.y.IsEven() ? 0x02 : 0x03;
		pubKey.x.Get32Bytes(publicKeyBytes + 1);
		sha256(publicKeyBytes, 33, hash);
	}
	else
	{
		publicKeyBytes[0] = 0x04;
		pubKey.x.Get32Bytes(publicKeyBytes + 1);
		pubKey.y.Get32Bytes(publicKeyBytes + 33);
		sha256(publicKeyBytes, 65, hash);
	}

	ripemd160(hash, 32, ripemd160_hash);

	addressBytes[0] = 0x00;
	memcpy(addressBytes + 1, ripemd160_hash, 20);

	sha256(addressBytes, 21, hash);
	sha256(hash, 32, hash);

	memcpy(addressBytes + 21, hash, 4);

	address = EncodeBase58(addressBytes, addressBytes + 25);
}

bool KeyHunt::checkPrivKey(std::string addr, Int &key, int32_t incr, bool mode)
{
	Int k(&key), k2(&key);
	k.Add((uint64_t)incr);
	k2.Add((uint64_t)incr);
	// Check addresses
	Point p = secp->ComputePublicKey(&k);
	std::string px = p.x.GetBase16();
	std::string chkAddr;
	GenerateBitcoinAddress(p, mode, chkAddr);
	if (chkAddr != addr)
	{
		// Key may be the opposite one (negative zero or compressed key)
		k.Neg();
		k.Add(&secp->order);
		p = secp->ComputePublicKey(&k);
		GenerateBitcoinAddress(p, mode, chkAddr);
		if (chkAddr != addr)
		{
			printf("\n=================================================================================\n");
			printf("Warning, wrong private key generated !\n");
			printf("  PivK :%s\n", k2.GetBase16().c_str());
			printf("  Addr :%s\n", addr.c_str());
			printf("  PubX :%s\n", px.c_str());
			printf("  PivK :%s\n", k.GetBase16().c_str());
			printf("  Check:%s\n", chkAddr.c_str());
			printf("  PubX :%s\n", p.x.GetBase16().c_str());
			printf("=================================================================================\n");
			return false;
		}
	}

	// Match found
	std::string result = "PubAddress: " + addr + "\n";
	result += "Priv (WIF): " + secp->GetPrivAddress(mode, k) + "\n";
	result += "Priv (HEX): " + k.GetBase16() + "\n";
	result += "PubK (HEX): " + secp->GetPublicKeyHex(mode, p) + "\n";
	result += "==========================================\n";

	// Write to file
	writeToFile(result);

	// Display in terminal
	printf("\nMatch found!\n%s", result.c_str());

	// Stop the search
	endOfSearch = true;

	return true;
}

bool KeyHunt::checkPrivKeyETH(std::string addr, Int &key, int32_t incr)
{
	Int k(&key), k2(&key);
	k.Add((uint64_t)incr);
	k2.Add((uint64_t)incr);
	// Check addresses
	Point p = secp->ComputePublicKey(&k);
	std::string px = p.x.GetBase16();
	std::string chkAddr = secp->GetAddressETH(p);
	if (chkAddr != addr)
	{
		// Key may be the opposite one (negative zero or compressed key)
		k.Neg();
		k.Add(&secp->order);
		p = secp->ComputePublicKey(&k);
		std::string chkAddr = secp->GetAddressETH(p);
		if (chkAddr != addr)
		{
			printf("\n=================================================================================\n");
			printf("Warning, wrong private key generated !\n");
			printf("  PivK :%s\n", k2.GetBase16().c_str());
			printf("  Addr :%s\n", addr.c_str());
			printf("  PubX :%s\n", px.c_str());
			printf("  PivK :%s\n", k.GetBase16().c_str());
			printf("  Check:%s\n", chkAddr.c_str());
			printf("  PubX :%s\n", p.x.GetBase16().c_str());
			printf("=================================================================================\n");
			return false;
		}
	}
	output(addr, k.GetBase16() /*secp->GetPrivAddressETH(k)*/, k.GetBase16(), secp->GetPublicKeyHexETH(p));
	return true;
}

bool KeyHunt::checkPrivKeyX(Int &key, int32_t incr, bool mode)
{
	Int k(&key);
	k.Add((uint64_t)incr);
	Point p = secp->ComputePublicKey(&k);
	std::string addr;
	GenerateBitcoinAddress(p, mode, addr);
	output(addr, secp->GetPrivAddress(mode, k), k.GetBase16(), secp->GetPublicKeyHex(mode, p));
	return true;
}

// ----------------------------------------------------------------------------

#ifdef WIN64
DWORD WINAPI _FindKeyCPU(LPVOID lpParam)
{
#else
void *_FindKeyCPU(void *lpParam)
{
#endif
	TH_PARAM *p = (TH_PARAM *)lpParam;
	p->obj->FindKeyCPU(p);
	return 0;
}

#ifdef WIN64
DWORD WINAPI _FindKeyGPU(LPVOID lpParam)
{
#else
void *_FindKeyGPU(void *lpParam)
{
#endif
	TH_PARAM *p = (TH_PARAM *)
		lpParam;
	p->obj->FindKeyGPU(p);
	return 0;
}

// ----------------------------------------------------------------------------

void KeyHunt::getCPUStartingKey(Int &tRangeStart, Int &tRangeEnd, Int &key, Point &startP)
{
	if (rKey <= 0)
	{
		key.Set(&tRangeStart);
	}
	else
	{
		Int diff(&tRangeEnd);
		diff.Sub(&tRangeStart);
		key.Rand(&diff);
		key.Add(&tRangeStart);

		// Ensure the key is within the range
		if (key.IsLower(&tRangeStart) || key.IsGreater(&tRangeEnd))
		{
			printf("Warning: Generated CPU key out of range. Regenerating...\n");
			getCPUStartingKey(tRangeStart, tRangeEnd, key, startP); // Recursive call to regenerate
			return;
		}
	}
	int bitLength = key.GetBitLength();
	printf("CPU starting key: %s (Bit length: %d)\n", key.GetBase16().c_str(), bitLength);

	Int km(&key);
	km.Add((uint64_t)CPU_GRP_SIZE / 2);
	startP = secp->ComputePublicKey(&km);
}

// ----------------------------------------------------------------------------

void KeyHunt::FindKeyCPU(TH_PARAM *ph)
{
	// Global init
	int thId = ph->threadId;
	Int tRangeStart = ph->rangeStart;
	Int tRangeEnd = ph->rangeEnd;
	counters[thId] = 0;

	// Add debug printing flag and sample size
	bool printDebugInfo = false; // Set this to false to disable debug printing
	int debugSampleSize = 10;	 // Number of keys to print for debugging
	int debugCounter = 0;		 // Counter for debug samples

	// CPU Thread
	IntGroup *grp = new IntGroup(CPU_GRP_SIZE / 2 + 1);

	// Group Init
	Int key;
	Point startP;
	getCPUStartingKey(tRangeStart, tRangeEnd, key, startP);

	Int *dx = new Int[CPU_GRP_SIZE / 2 + 1];
	Point *pts = new Point[CPU_GRP_SIZE];

	Int *dy = new Int();
	Int *dyn = new Int();
	Int *_s = new Int();
	Int *_p = new Int();
	Point *pp = new Point();
	Point *pn = new Point();
	grp->Set(dx);

	ph->hasStarted = true;
	ph->rKeyRequest = false;

	while (!endOfSearch)
	{
		if (fullyRandom)
		{
			// Generate a new random key within the thread's range
			key.Rand(&tRangeEnd);
			key.Add(&tRangeStart);
			startP = secp->ComputePublicKey(&key);
		}
		else if (ph->rKeyRequest)
		{
			getCPUStartingKey(tRangeStart, tRangeEnd, key, startP);
			ph->rKeyRequest = false;
		}

		// Fill group
		int i;
		int hLength = (CPU_GRP_SIZE / 2 - 1);

		for (i = 0; i < hLength; i++)
		{
			dx[i].ModSub(&Gn[i].x, &startP.x);
		}
		dx[i].ModSub(&Gn[i].x, &startP.x);	  // For the first point
		dx[i + 1].ModSub(&_2Gn.x, &startP.x); // For the next center point

		// Grouped ModInv
		grp->ModInv();

		// We use the fact that P + i*G and P - i*G has the same deltax, so the same inverse
		// We compute key in the positive and negative way from the center of the group

		// center point
		pts[CPU_GRP_SIZE / 2] = startP;

		for (i = 0; i < hLength && !endOfSearch; i++)
		{
			*pp = startP;
			*pn = startP;

			// P = startP + i*G
			dy->ModSub(&Gn[i].y, &pp->y);

			_s->ModMulK1(dy, &dx[i]); // s = (p2.y-p1.y)*inverse(p2.x-p1.x);
			_p->ModSquareK1(_s);	  // _p = pow2(s)

			pp->x.ModNeg();
			pp->x.ModAdd(_p);
			pp->x.ModSub(&Gn[i].x); // rx = pow2(s) - p1.x - p2.x;

			pp->y.ModSub(&Gn[i].x, &pp->x);
			pp->y.ModMulK1(_s);
			pp->y.ModSub(&Gn[i].y); // ry = - p2.y - s*(ret.x-p2.x);

			// P = startP - i*G  , if (x,y) = i*G then (x,-y) = -i*G
			dyn->Set(&Gn[i].y);
			dyn->ModNeg();
			dyn->ModSub(&pn->y);

			_s->ModMulK1(dyn, &dx[i]); // s = (p2.y-p1.y)*inverse(p2.x-p1.x);
			_p->ModSquareK1(_s);	   // _p = pow2(s)

			pn->x.ModNeg();
			pn->x.ModAdd(_p);
			pn->x.ModSub(&Gn[i].x); // rx = pow2(s) - p1.x - p2.x;

			pn->y.ModSub(&Gn[i].x, &pn->x);
			pn->y.ModMulK1(_s);
			pn->y.ModAdd(&Gn[i].y); // ry = - p2.y - s*(ret.x-p2.x);

			pts[CPU_GRP_SIZE / 2 + (i + 1)] = *pp;
			pts[CPU_GRP_SIZE / 2 - (i + 1)] = *pn;
		}

		// First point (startP - (GRP_SZIE/2)*G)
		*pn = startP;
		dyn->Set(&Gn[i].y);
		dyn->ModNeg();
		dyn->ModSub(&pn->y);

		_s->ModMulK1(dyn, &dx[i]);
		_p->ModSquareK1(_s);

		pn->x.ModNeg();
		pn->x.ModAdd(_p);
		pn->x.ModSub(&Gn[i].x);

		pn->y.ModSub(&Gn[i].x, &pn->x);
		pn->y.ModMulK1(_s);
		pn->y.ModAdd(&Gn[i].y);

		pts[0] = *pn;

		// Next start point (startP + GRP_SIZE*G)
		*pp = startP;
		dy->ModSub(&_2Gn.y, &pp->y);

		_s->ModMulK1(dy, &dx[i + 1]);
		_p->ModSquareK1(_s);

		pp->x.ModNeg();
		pp->x.ModAdd(_p);
		pp->x.ModSub(&_2Gn.x);

		pp->y.ModSub(&_2Gn.x, &pp->x);
		pp->y.ModMulK1(_s);
		pp->y.ModSub(&_2Gn.y);
		startP = *pp;

		// Check addresses
		if (useSSE)
		{
			for (int i = 0; i < CPU_GRP_SIZE && !endOfSearch; i += 4)
			{
				switch (compMode)
				{
				case SEARCH_COMPRESSED:
					if (searchMode == (int)SEARCH_MODE_MA)
					{
						checkMultiAddressesSSE(true, key, i, pts[i], pts[i + 1], pts[i + 2], pts[i + 3]);
					}
					else if (searchMode == (int)SEARCH_MODE_SA)
					{
						checkSingleAddressesSSE(true, key, i, pts[i], pts[i + 1], pts[i + 2], pts[i + 3]);
					}
					break;
				case SEARCH_UNCOMPRESSED:
					if (searchMode == (int)SEARCH_MODE_MA)
					{
						checkMultiAddressesSSE(false, key, i, pts[i], pts[i + 1], pts[i + 2], pts[i + 3]);
					}
					else if (searchMode == (int)SEARCH_MODE_SA)
					{
						checkSingleAddressesSSE(false, key, i, pts[i], pts[i + 1], pts[i + 2], pts[i + 3]);
					}
					break;
				case SEARCH_BOTH:
					if (searchMode == (int)SEARCH_MODE_MA)
					{
						checkMultiAddressesSSE(true, key, i, pts[i], pts[i + 1], pts[i + 2], pts[i + 3]);
						checkMultiAddressesSSE(false, key, i, pts[i], pts[i + 1], pts[i + 2], pts[i + 3]);
					}
					else if (searchMode == (int)SEARCH_MODE_SA)
					{
						checkSingleAddressesSSE(true, key, i, pts[i], pts[i + 1], pts[i + 2], pts[i + 3]);
						checkSingleAddressesSSE(false, key, i, pts[i], pts[i + 1], pts[i + 2], pts[i + 3]);
					}
					break;
				}
			}
		}
		else
		{
			if (coinType == COIN_BTC)
			{
				for (int i = 0; i < CPU_GRP_SIZE && !endOfSearch; i++)
				{
					// Debug printing
					if (printDebugInfo && debugCounter < debugSampleSize)
					{
						Int privateKey(&key);
						privateKey.Add((uint64_t)i);
						Point publicKey = secp->ComputePublicKey(&privateKey);
						std::string compressedAddr, uncompressedAddr;

						GenerateBitcoinAddress(publicKey, true, compressedAddr);
						GenerateBitcoinAddress(publicKey, false, uncompressedAddr);

						printf("\nCPU Debug Info (BTC, Sample %d):\n", debugCounter + 1);
						printf("Private Key: %s\n", privateKey.GetBase16().c_str());
						printf("Public Key: (%s, %s)\n", publicKey.x.GetBase16().c_str(), publicKey.y.GetBase16().c_str());
						printf("Compressed Address: %s\n", compressedAddr.c_str());
						printf("Uncompressed Address: %s\n", uncompressedAddr.c_str());
						printf("--------------------\n");

						debugCounter++;
					}

					switch (compMode)
					{
					case SEARCH_COMPRESSED:
						switch (searchMode)
						{
						case (int)SEARCH_MODE_MA:
							checkMultiAddresses(true, key, i, pts[i]);
							break;
						case (int)SEARCH_MODE_SA:
							checkSingleAddress(true, key, i, pts[i]);
							break;
						case (int)SEARCH_MODE_MX:
							checkMultiXPoints(true, key, i, pts[i]);
							break;
						case (int)SEARCH_MODE_SX:
							checkSingleXPoint(true, key, i, pts[i]);
							break;
						default:
							break;
						}
						break;
					case SEARCH_UNCOMPRESSED:
						switch (searchMode)
						{
						case (int)SEARCH_MODE_MA:
							checkMultiAddresses(false, key, i, pts[i]);
							break;
						case (int)SEARCH_MODE_SA:
							checkSingleAddress(false, key, i, pts[i]);
							break;
						case (int)SEARCH_MODE_MX:
							checkMultiXPoints(false, key, i, pts[i]);
							break;
						case (int)SEARCH_MODE_SX:
							checkSingleXPoint(false, key, i, pts[i]);
							break;
						default:
							break;
						}
						break;
					case SEARCH_BOTH:
						switch (searchMode)
						{
						case (int)SEARCH_MODE_MA:
							checkMultiAddresses(true, key, i, pts[i]);
							checkMultiAddresses(false, key, i, pts[i]);
							break;
						case (int)SEARCH_MODE_SA:
							checkSingleAddress(true, key, i, pts[i]);
							checkSingleAddress(false, key, i, pts[i]);
							break;
						case (int)SEARCH_MODE_MX:
							checkMultiXPoints(true, key, i, pts[i]);
							checkMultiXPoints(false, key, i, pts[i]);
							break;
						case (int)SEARCH_MODE_SX:
							checkSingleXPoint(true, key, i, pts[i]);
							checkSingleXPoint(false, key, i, pts[i]);
							break;
						default:
							break;
						}
						break;
					}
				}
			}
			else
			{
				for (int i = 0; i < CPU_GRP_SIZE && !endOfSearch; i++)
				{
					// Debug printing for ETH
					if (printDebugInfo && debugCounter < debugSampleSize)
					{
						Int privateKey(&key);
						privateKey.Add((uint64_t)i);
						Point publicKey = secp->ComputePublicKey(&privateKey);
						std::string ethAddr = secp->GetAddressETH(publicKey);

						printf("\nCPU Debug Info (ETH, Sample %d):\n", debugCounter + 1);
						printf("Private Key: %s\n", privateKey.GetBase16().c_str());
						printf("Public Key: (%s, %s)\n", publicKey.x.GetBase16().c_str(), publicKey.y.GetBase16().c_str());
						printf("ETH Address: %s\n", ethAddr.c_str());
						printf("--------------------\n");

						debugCounter++;
					}

					switch (searchMode)
					{
					case (int)SEARCH_MODE_MA:
						checkMultiAddressesETH(key, i, pts[i]);
						break;
					case (int)SEARCH_MODE_SA:
						checkSingleAddressETH(key, i, pts[i]);
						break;
					default:
						break;
					}
				}
			}
		}

		if (!fullyRandom)
		{
			key.Add((uint64_t)CPU_GRP_SIZE);
		}
		counters[thId] += CPU_GRP_SIZE; // Point
	}
	ph->isRunning = false;

	delete grp;
	delete[] dx;
	delete[] pts;

	delete dy;
	delete dyn;
	delete _s;
	delete _p;
	delete pp;
	delete pn;
}
// ----------------------------------------------------------------------------

void KeyHunt::getGPUStartingKeys(Int &tRangeStart, Int &tRangeEnd, int groupSize, int nbThread, Int *keys, Point *p)
{
	if (useSegment)
	{
		// Segmented mode
		maxThreads = nbThread;
		if (rangeDiffs == nullptr)
		{
			rangeDiffs = new Int[maxThreads];
		}

		Int rangeSize = tRangeEnd;
		rangeSize.Sub(&tRangeStart);
		Int threadRangeSize = rangeSize;
		Int nbThreadsInt;
		nbThreadsInt.SetInt32(maxThreads);
		threadRangeSize.Div(&nbThreadsInt);

		if (printDebug)
		{
			printf("Debug: Segmented mode. Total range: [%s, %s]\n",
				   tRangeStart.GetBase16().c_str(), tRangeEnd.GetBase16().c_str());
		}

		for (int i = 0; i < maxThreads; i++)
		{
			Int threadStart = tRangeStart;
			Int iInt;
			iInt.SetInt32(i);
			Int offset;
			offset.Set(&threadRangeSize);
			offset.Mult(&iInt);
			threadStart.Add(&offset);
			Int threadEnd = threadStart;
			threadEnd.Add(&threadRangeSize);
			if (i == maxThreads - 1)
			{
				threadEnd.Set(&tRangeEnd); // Ensure the last thread covers up to the range end
			}

			rangeDiffs[i].Set(&threadEnd);
			rangeDiffs[i].Sub(&threadStart);

			if (rKey > 0)
			{
				// Generate a random key within the thread's range
				keys[i].Rand(&rangeDiffs[i]);
				keys[i].Add(&threadStart);
			}
			else
			{
				keys[i].Set(&threadStart);
			}

			// Compute the public key
			Int k;
			k.Set(&keys[i]);
			Int halfGroupSize;
			halfGroupSize.SetInt32(groupSize / 2);
			k.Add(&halfGroupSize);
			p[i] = secp->ComputePublicKey(&k);

			if (printDebug)
			{
				printf("Debug: Thread %d range: [%s, %s]\n", i,
					   threadStart.GetBase16().c_str(), threadEnd.GetBase16().c_str());
				printf("Debug: Thread %d starting key: %s\n", i, keys[i].GetBase16().c_str());
			}
		}
	}
	else
	{
		// Original non-segmented mode
		Int tRangeDiff;
		tRangeDiff.Set(&tRangeEnd);
		tRangeDiff.Sub(&tRangeStart);

		if (printDebug)
		{
			printf("Debug: Non-segmented mode. Range: [%s, %s]\n",
				   tRangeStart.GetBase16().c_str(), tRangeEnd.GetBase16().c_str());
		}

		for (int i = 0; i < nbThread; i++)
		{
			keys[i].Set(&tRangeStart);

			if (rKey > 0)
			{
				Int randomPart;
				randomPart.Rand(tRangeDiff.GetBitLength());
				keys[i].Add(&randomPart);

				// Ensure the key is within the range
				if (keys[i].IsGreater(&tRangeEnd))
				{
					keys[i].Set(&tRangeEnd);
					keys[i].Sub(&tRangeDiff);
					Int two;
					two.SetInt32(2);
					keys[i].Div(&two); // Set to middle of range if over
				}
				if (keys[i].IsLower(&tRangeStart))
				{
					keys[i].Set(&tRangeStart);
				}
			}

			Int k;
			k.Set(&keys[i]);
			Int halfGroupSize;
			halfGroupSize.SetInt32(groupSize / 2);
			k.Add(&halfGroupSize);
			p[i] = secp->ComputePublicKey(&k);

			if (printDebug)
			{
				printf("Debug: Thread %d key: %s\n", i, keys[i].GetBase16().c_str());
			}
		}
	}

	if (printDebug)
	{
		printf("Debug: getGPUStartingKeys completed.\n");
	}
}

// ----------------------------------------------------------------------------

void KeyHunt::FindKeyGPU(TH_PARAM *ph)
{
	bool ok = true;

#ifdef WITHGPU

	int thId = ph->threadId;
	Int tRangeStart = ph->rangeStart;
	Int tRangeEnd = ph->rangeEnd;

	GPUEngine *g = nullptr;
	try
	{
		switch (searchMode)
		{
		case (int)SEARCH_MODE_MA:
		case (int)SEARCH_MODE_MX:
			g = new GPUEngine(secp, ph->gridSizeX, ph->gridSizeY, ph->gpuId, maxFound, searchMode, compMode, coinType,
							  BLOOM_N, bloom->get_bits(), bloom->get_hashes(), bloom->get_bf(), DATA, TOTAL_COUNT, (rKey != 0));
			break;
		case (int)SEARCH_MODE_SA:
			g = new GPUEngine(secp, ph->gridSizeX, ph->gridSizeY, ph->gpuId, maxFound, searchMode, compMode, coinType,
							  hash160Keccak, (rKey != 0));
			break;
		case (int)SEARCH_MODE_SX:
			g = new GPUEngine(secp, ph->gridSizeX, ph->gridSizeY, ph->gpuId, maxFound, searchMode, compMode, coinType,
							  xpoint, (rKey != 0));
			break;
		default:
			printf("Invalid search mode format\n");
			return;
		}
	}
	catch (const std::exception &e)
	{
		printf("Exception during GPUEngine initialization: %s\n", e.what());
		return;
	}

	if (g == nullptr)
	{
		printf("Failed to initialize GPUEngine\n");
		return;
	}

	int nbThread = g->GetNbThread();
	Point *p = new Point[nbThread];
	Int *keys = new Int[nbThread];
	std::vector<ITEM> found;

	printf("GPU: %s, nbThread = %d\n", g->deviceName.c_str(), nbThread);

	counters[thId] = 0;

	getGPUStartingKeys(tRangeStart, tRangeEnd, g->GetGroupSize(), nbThread, keys, p);
	ok = g->SetKeys(p);

	ph->hasStarted = true;
	ph->rKeyRequest = false;

	uint64_t lastDebugUpdate = 0;

	// GPU Thread
	while (ok && !endOfSearch)
	{
		if (fullyRandom)
		{
			// Generate new random keys for each thread
			for (int i = 0; i < nbThread; i++)
			{
				keys[i].Rand(&tRangeEnd);
				keys[i].Add(&tRangeStart);
				p[i] = secp->ComputePublicKey(&keys[i]);
			}
			ok = g->SetKeys(p);
		}
		else if (ph->rKeyRequest)
		{
			getGPUStartingKeys(tRangeStart, tRangeEnd, g->GetGroupSize(), nbThread, keys, p);
			ok = g->SetKeys(p);
			ph->rKeyRequest = false;
		}

		// Call kernel
		found.clear();
		switch (searchMode)
		{
		case (int)SEARCH_MODE_MA:
			ok = g->LaunchSEARCH_MODE_MA(found, false);
			break;
		case (int)SEARCH_MODE_MX:
			ok = g->LaunchSEARCH_MODE_MX(found, false);
			break;
		case (int)SEARCH_MODE_SA:
			ok = g->LaunchSEARCH_MODE_SA(found, false);
			break;
		case (int)SEARCH_MODE_SX:
			ok = g->LaunchSEARCH_MODE_SX(found, false);
			break;
		default:
			printf("Invalid search mode in kernel launch\n");
			ok = false;
			break;
		}

		for (int i = 0; i < (int)found.size() && !endOfSearch; i++)
		{
			ITEM it = found[i];
			bool keyFound = false;

			if (coinType == COIN_BTC)
			{
				std::string addr;
				Point pubKey = secp->ComputePublicKey(&keys[it.thId]);

				// Compute the increment point
				Int incr;
				incr.SetInt32((int32_t)it.incr);
				Point incrPoint = secp->ComputePublicKey(&incr);

				// Add the increment to the public key
				pubKey = secp->AddDirect(pubKey, incrPoint);

				GenerateBitcoinAddress(pubKey, it.mode, addr);
				keyFound = checkPrivKey(addr, keys[it.thId], it.incr, it.mode);
			}
			else
			{
				std::string addr = secp->GetAddressETH(it.hash);
				keyFound = checkPrivKeyETH(addr, keys[it.thId], it.incr);
			}

			if (keyFound)
			{
				nbFoundKey++;
			}
		}

		if (ok && !fullyRandom)
		{
			for (int i = 0; i < nbThread; i++)
			{
				keys[i].Add((uint64_t)STEP_SIZE);

				if (useSegment)
				{
					// Ensure the key stays within its assigned range
					if (keys[i].IsGreater(&tRangeEnd))
					{
						keys[i].Set(&tRangeStart);
						keys[i].Add(&rangeDiffs[i]);
					}
				}
			}
		}
		counters[thId] += (uint64_t)(STEP_SIZE)*nbThread;

		// Debug output
		if (printDebug && (counters[thId] - lastDebugUpdate >= debugUpdateInterval))
		{
			lastDebugUpdate = counters[thId];
			printf("\nDebug info (GPU Thread %d, Counter: %lu):\n", thId, counters[thId]);
			for (int i = 0; i < nbThread; i++)
			{
				Int privateKey(&keys[i]);
				Point publicKey = secp->ComputePublicKey(&privateKey);

				printf("Thread %d:\n", i);
				printf("Private Key: %s\n", privateKey.GetBase16().c_str());
				printf("Public Key: (%s, %s)\n", publicKey.x.GetBase16().c_str(), publicKey.y.GetBase16().c_str());

				if (coinType == COIN_BTC)
				{
					std::string compressedAddr, uncompressedAddr;
					GenerateBitcoinAddress(publicKey, true, compressedAddr);
					GenerateBitcoinAddress(publicKey, false, uncompressedAddr);
					printf("BTC Address (Compressed): %s\n", compressedAddr.c_str());
					printf("BTC Address (Uncompressed): %s\n", uncompressedAddr.c_str());
				}
				else
				{
					std::string ethAddr = secp->GetAddressETH(publicKey);
					printf("ETH Address: %s\n", ethAddr.c_str());
				}
				printf("--------------------\n");
			}
		}
	}

	delete[] keys;
	delete[] p;
	delete g;

#else
	ph->hasStarted = true;
	printf("GPU code not compiled, use -DWITHGPU when compiling.\n");
#endif

	ph->isRunning = false;
}
// ----------------------------------------------------------------------------

bool KeyHunt::isAlive(TH_PARAM *p)
{

	bool isAlive = true;
	int total = nbCPUThread + nbGPUThread;
	for (int i = 0; i < total; i++)
		isAlive = isAlive && p[i].isRunning;

	return isAlive;
}

// ----------------------------------------------------------------------------

bool KeyHunt::hasStarted(TH_PARAM *p)
{

	bool hasStarted = true;
	int total = nbCPUThread + nbGPUThread;
	for (int i = 0; i < total; i++)
		hasStarted = hasStarted && p[i].hasStarted;

	return hasStarted;
}

// ----------------------------------------------------------------------------

uint64_t KeyHunt::getGPUCount()
{

	uint64_t count = 0;
	for (int i = 0; i < nbGPUThread; i++)
		count += counters[0x80L + i];
	return count;
}

// ----------------------------------------------------------------------------

uint64_t KeyHunt::getCPUCount()
{

	uint64_t count = 0;
	for (int i = 0; i < nbCPUThread; i++)
		count += counters[i];
	return count;
}

// ----------------------------------------------------------------------------

void KeyHunt::rKeyRequest(TH_PARAM *p)
{
	int total = nbCPUThread + nbGPUThread;
	Int newKey;
	Int rangeDiff(&rangeEnd);
	rangeDiff.Sub(&rangeStart);

	// printf("Debug: rKeyRequest called. Range start: %s, Range end: %s\n",
	// rangeStart.GetBase16().c_str(), rangeEnd.GetBase16().c_str());

	for (int i = 0; i < total; i++)
	{
		p[i].rKeyRequest = true;

		if (rKey > 0)
		{
			newKey.Rand(rangeDiff.GetBitLength());
			newKey.Add(&rangeStart);

			// printf("Debug: Generated key for thread %d: %s\n", i, newKey.GetBase16().c_str());

			// Ensure the key is within the range
			if (newKey.IsLower(&rangeStart) || newKey.IsGreater(&rangeEnd))
			{
				// printf("Debug: Generated key out of range for thread %d. Adjusting.\n", i);
				if (newKey.IsLower(&rangeStart))
				{
					newKey.Set(&rangeStart);
				}
				else
				{
					newKey.Set(&rangeEnd);
					newKey.Sub(&rangeDiff);
					Int two;
					two.SetInt32(2);
					newKey.Div(&two); // Set to middle of range if over
				}
				// printf("Debug: Adjusted key for thread %d: %s\n", i, newKey.GetBase16().c_str());
			}

			p[i].rangeStart.Set(&newKey);

			if (i == 0)
			{
				// Update the global rangeStart with the first thread's new key
				rangeStart.Set(&newKey);
				// printf("Debug: Updated global rangeStart: %s\n", rangeStart.GetBase16().c_str());
			}
		}
	}

	// printf("Debug: rKeyRequest completed.\n");
}
// ----------------------------------------------------------------------------

void KeyHunt::SetupRanges(uint32_t totalThreads)
{
	Int threads;
	threads.SetInt32(totalThreads);
	rangeDiff.Set(&rangeEnd);
	rangeDiff.Sub(&rangeStart);
	rangeDiff.Div(&threads);
}

// ----------------------------------------------------------------------------

void KeyHunt::Search(int nbThread, std::vector<int> gpuId, std::vector<int> gridSize, bool &should_exit)
{
	double t0;
	double t1;
	endOfSearch = false;
	nbCPUThread = nbThread;
	nbGPUThread = (useGpu ? (int)gpuId.size() : 0);
	nbFoundKey = 0;

	// setup ranges
	SetupRanges(nbCPUThread + nbGPUThread);

	memset(counters, 0, sizeof(counters));

	if (!useGpu)
		printf("\n");

	TH_PARAM *params = (TH_PARAM *)malloc((nbCPUThread + nbGPUThread) * sizeof(TH_PARAM));
	memset(params, 0, (nbCPUThread + nbGPUThread) * sizeof(TH_PARAM));

	// Launch CPU threads
	for (int i = 0; i < nbCPUThread; i++)
	{
		params[i].obj = this;
		params[i].threadId = i;
		params[i].isRunning = true;

		params[i].rangeStart.Set(&rangeStart);
		rangeStart.Add(&rangeDiff);
		params[i].rangeEnd.Set(&rangeStart);

#ifdef WIN64
		DWORD thread_id;
		CreateThread(NULL, 0, _FindKeyCPU, (void *)(params + i), 0, &thread_id);
		ghMutex = CreateMutex(NULL, FALSE, NULL);
#else
		pthread_t thread_id;
		pthread_create(&thread_id, NULL, &_FindKeyCPU, (void *)(params + i));
		ghMutex = PTHREAD_MUTEX_INITIALIZER;
#endif
	}

	// Launch GPU threads
	for (int i = 0; i < nbGPUThread; i++)
	{
		params[nbCPUThread + i].obj = this;
		params[nbCPUThread + i].threadId = 0x80L + i;
		params[nbCPUThread + i].isRunning = true;
		params[nbCPUThread + i].gpuId = gpuId[i];
		params[nbCPUThread + i].gridSizeX = gridSize[2 * i];
		params[nbCPUThread + i].gridSizeY = gridSize[2 * i + 1];

		params[nbCPUThread + i].rangeStart.Set(&rangeStart);
		rangeStart.Add(&rangeDiff);
		params[nbCPUThread + i].rangeEnd.Set(&rangeStart);

#ifdef WIN64
		DWORD thread_id;
		CreateThread(NULL, 0, _FindKeyGPU, (void *)(params + (nbCPUThread + i)), 0, &thread_id);
#else
		pthread_t thread_id;
		pthread_create(&thread_id, NULL, &_FindKeyGPU, (void *)(params + (nbCPUThread + i)));
#endif
	}

#ifndef WIN64
	setvbuf(stdout, NULL, _IONBF, 0);
#endif
	printf("\n");

	uint64_t lastCount = 0;
	uint64_t gpuCount = 0;
	uint64_t lastGPUCount = 0;

	// Key rate smoothing filter
#define FILTER_SIZE 8
	double lastkeyRate[FILTER_SIZE];
	double lastGpukeyRate[FILTER_SIZE];
	uint32_t filterPos = 0;

	double keyRate = 0.0;
	double gpuKeyRate = 0.0;
	char timeStr[256];

	memset(lastkeyRate, 0, sizeof(lastkeyRate));
	memset(lastGpukeyRate, 0, sizeof(lastkeyRate));

	// Wait that all threads have started
	while (!hasStarted(params))
	{
		Timer::SleepMillis(500);
	}

	// Reset timer
	Timer::Init();
	t0 = Timer::get_tick();
	startTime = t0;
	Int p100;
	Int ICount;
	p100.SetInt32(100);
	Int completedPerc;
	completedPerc.SetInt32(0);
	uint64_t rKeyCount = 0;

	while (isAlive(params) && !endOfSearch)
	{
		int delay = 2000;
		while (isAlive(params) && delay > 0 && !endOfSearch)
		{
			Timer::SleepMillis(500);
			delay -= 500;
		}

		if (endOfSearch)
			break;

		gpuCount = getGPUCount();
		uint64_t count = getCPUCount() + gpuCount;
		ICount.SetInt64(count);
		int completedBits = ICount.GetBitLength();

		if (rKey <= 0)
		{
			Int rangeTotal(&rangeEnd);
			rangeTotal.Sub(&rangeStart);
			if (!rangeTotal.IsZero())
			{
				Int rangeDone(&ICount);
				rangeDone.Sub(&rangeStart);
				rangeDone.Mult(&p100);
				completedPerc.Set(&rangeDone);
				completedPerc.Div(&rangeTotal);
			}
			else
			{
				completedPerc.SetInt32(100);
			}
		}

		t1 = Timer::get_tick();
		keyRate = (double)(count - lastCount) / (t1 - t0);
		gpuKeyRate = (double)(gpuCount - lastGPUCount) / (t1 - t0);
		lastkeyRate[filterPos % FILTER_SIZE] = keyRate;
		lastGpukeyRate[filterPos % FILTER_SIZE] = gpuKeyRate;
		filterPos++;

		// KeyRate smoothing
		double avgKeyRate = 0.0;
		double avgGpuKeyRate = 0.0;
		uint32_t nbSample;
		for (nbSample = 0; (nbSample < FILTER_SIZE) && (nbSample < filterPos); nbSample++)
		{
			avgKeyRate += lastkeyRate[nbSample];
			avgGpuKeyRate += lastGpukeyRate[nbSample];
		}
		avgKeyRate /= (double)(nbSample);
		avgGpuKeyRate /= (double)(nbSample);

		if (isAlive(params))
		{
			memset(timeStr, '\0', 256);

			// Randomly select a thread
			std::uniform_int_distribution<> dis(0, nbCPUThread + nbGPUThread - 1);
			int randomThread = dis(gen);

			printf("\r[%s] [CPU+GPU: %.2f Mk/s] [GPU: %.2f Mk/s] [C: %s %%] [R: %lu] [T: %s (%d bit)] [F: %d] [Thread %d key: %s] ",
				   toTimeStr(t1, timeStr),
				   avgKeyRate / 1000000.0,
				   avgGpuKeyRate / 1000000.0,
				   completedPerc.GetBase10().c_str(),
				   rKeyCount,
				   formatThousands(count).c_str(),
				   completedBits,
				   nbFoundKey,
				   randomThread,
				   params[randomThread].rangeStart.GetBase16().c_str());

			if (rKey > 0)
			{
				// printf("[Range Start: %s] ", rangeStart.GetBase16().c_str());
			}
		}

		if (rKey > 0)
		{
			if ((count - lastrKey) > (1000000 * rKey))
			{
				// rKey request
				rKeyRequest(params);
				lastrKey = count;
				rKeyCount++;

				// Update rangeStart to reflect the new starting point
				if (nbCPUThread > 0)
				{
					rangeStart.Set(&params[0].rangeStart);
				}
				else if (nbGPUThread > 0)
				{
					rangeStart.Set(&params[nbCPUThread].rangeStart);
				}
			}
		}

		lastCount = count;
		lastGPUCount = gpuCount;
		t0 = t1;
		if (should_exit || nbFoundKey >= targetCounter || completedPerc.IsGreaterOrEqual(&p100))
			endOfSearch = true;
	}

	// Display final message
	if (endOfSearch && nbFoundKey > 0)
	{
		printf("\n\nSearch completed. Key found and saved to FOUNDKEY.txt\n");
	}
	else
	{
		printf("\n\nSearch completed. No matching key found.\n");
	}

	free(params);
}
// ----------------------------------------------------------------------------

std::string KeyHunt::GetHex(std::vector<unsigned char> &buffer)
{
	std::string ret;

	char tmp[128];
	for (int i = 0; i < (int)buffer.size(); i++)
	{
		sprintf(tmp, "%02X", buffer[i]);
		ret.append(tmp);
	}
	return ret;
}

// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------

int KeyHunt::CheckBloomBinary(const uint8_t *_xx, uint32_t K_LENGTH)
{
	if (bloom->check(_xx, K_LENGTH) > 0)
	{
		uint8_t *temp_read;
		uint64_t half, min, max, current; //, current_offset
		int64_t rcmp;
		int32_t r = 0;
		min = 0;
		current = 0;
		max = TOTAL_COUNT;
		half = TOTAL_COUNT;
		while (!r && half >= 1)
		{
			half = (max - min) / 2;
			temp_read = DATA + ((current + half) * K_LENGTH);
			rcmp = memcmp(_xx, temp_read, K_LENGTH);
			if (rcmp == 0)
			{
				r = 1; // Found!!
			}
			else
			{
				if (rcmp < 0)
				{ // data < temp_read
					max = (max - half);
				}
				else
				{ // data > temp_read
					min = (min + half);
				}
				current = min;
			}
		}
		return r;
	}
	return 0;
}

// ----------------------------------------------------------------------------

bool KeyHunt::MatchHash(uint32_t *_h)
{
	if (_h[0] == hash160Keccak[0] &&
		_h[1] == hash160Keccak[1] &&
		_h[2] == hash160Keccak[2] &&
		_h[3] == hash160Keccak[3] &&
		_h[4] == hash160Keccak[4])
	{
		return true;
	}
	else
	{
		return false;
	}
}

// ----------------------------------------------------------------------------

bool KeyHunt::MatchXPoint(uint32_t *_h)
{
	if (_h[0] == xpoint[0] &&
		_h[1] == xpoint[1] &&
		_h[2] == xpoint[2] &&
		_h[3] == xpoint[3] &&
		_h[4] == xpoint[4] &&
		_h[5] == xpoint[5] &&
		_h[6] == xpoint[6] &&
		_h[7] == xpoint[7])
	{
		return true;
	}
	else
	{
		return false;
	}
}

// ----------------------------------------------------------------------------

std::string KeyHunt::formatThousands(uint64_t x)
{
	char buf[32] = "";

	sprintf(buf, "%lu", x); // Changed from %llu to %lu

	std::string s(buf);

	int len = (int)s.length();

	int numCommas = (len - 1) / 3;

	if (numCommas == 0)
	{
		return s;
	}

	std::string result = "";

	int count = ((len % 3) == 0) ? 0 : (3 - (len % 3));

	for (int i = 0; i < len; i++)
	{
		result += s[i];

		if (count++ == 2 && i < len - 1)
		{
			result += ",";
			count = 0;
		}
	}
	return result;
}

// ----------------------------------------------------------------------------

char *KeyHunt::toTimeStr(int sec, char *timeStr)
{
	int h, m, s;
	h = (sec / 3600);
	m = (sec - (3600 * h)) / 60;
	s = (sec - (3600 * h) - (m * 60));
	sprintf(timeStr, "%0*d:%0*d:%0*d", 2, h, 2, m, 2, s);
	return (char *)timeStr;
}

// ----------------------------------------------------------------------------

double KeyHunt::CalcPercantage(Int &n, Int &d, Int &m)
{
	// Use n to calculate percentage
	Int r = n;
	r.Mult(&m);
	r.Div(&d);
	return (double)r.GetInt32() / (double)m.GetInt32() * 100.0;
}

// ----------------------------------------------------------------------------

void KeyHunt::checkSingleAddressETH(Int key, int i, Point p1)
{
	unsigned char h0[20];
	secp->GetHashETH(p1, h0);
	if (MatchHash((uint32_t *)h0))
	{
		std::string addr = secp->GetAddressETH(h0);
		if (checkPrivKeyETH(addr, key, i))
		{
			nbFoundKey++;
		}
	}
}

void KeyHunt::checkMultiAddressesETH(Int key, int i, Point p1)
{
	unsigned char h0[20];
	secp->GetHashETH(p1, h0);
	if (CheckBloomBinary(h0, 20) > 0)
	{
		std::string addr = secp->GetAddressETH(h0);
		if (checkPrivKeyETH(addr, key, i))
		{
			nbFoundKey++;
		}
	}
}

void KeyHunt::checkSingleAddressesSSE(bool compressed, Int key, int i, Point p1, Point p2, Point p3, Point p4)
{
	unsigned char h0[20];
	unsigned char h1[20];
	unsigned char h2[20];
	unsigned char h3[20];

	secp->GetHash160(compressed, p1, p2, p3, p4, h0, h1, h2, h3);

	if (MatchHash((uint32_t *)h0))
	{
		std::string addr;
		GenerateBitcoinAddress(p1, compressed, addr);
		if (checkPrivKey(addr, key, i + 0, compressed))
		{
			nbFoundKey++;
		}
	}
	if (MatchHash((uint32_t *)h1))
	{
		std::string addr;
		GenerateBitcoinAddress(p2, compressed, addr);
		if (checkPrivKey(addr, key, i + 1, compressed))
		{
			nbFoundKey++;
		}
	}
	if (MatchHash((uint32_t *)h2))
	{
		std::string addr;
		GenerateBitcoinAddress(p3, compressed, addr);
		if (checkPrivKey(addr, key, i + 2, compressed))
		{
			nbFoundKey++;
		}
	}
	if (MatchHash((uint32_t *)h3))
	{
		std::string addr;
		GenerateBitcoinAddress(p4, compressed, addr);
		if (checkPrivKey(addr, key, i + 3, compressed))
		{
			nbFoundKey++;
		}
	}
}

void KeyHunt::checkMultiAddressesSSE(bool compressed, Int key, int i, Point p1, Point p2, Point p3, Point p4)
{
	unsigned char h0[20];
	unsigned char h1[20];
	unsigned char h2[20];
	unsigned char h3[20];

	secp->GetHash160(compressed, p1, p2, p3, p4, h0, h1, h2, h3);

	if (CheckBloomBinary(h0, 20) > 0)
	{
		std::string addr;
		GenerateBitcoinAddress(p1, compressed, addr);
		if (checkPrivKey(addr, key, i + 0, compressed))
		{
			nbFoundKey++;
		}
	}
	if (CheckBloomBinary(h1, 20) > 0)
	{
		std::string addr;
		GenerateBitcoinAddress(p2, compressed, addr);
		if (checkPrivKey(addr, key, i + 1, compressed))
		{
			nbFoundKey++;
		}
	}
	if (CheckBloomBinary(h2, 20) > 0)
	{
		std::string addr;
		GenerateBitcoinAddress(p3, compressed, addr);
		if (checkPrivKey(addr, key, i + 2, compressed))
		{
			nbFoundKey++;
		}
	}
	if (CheckBloomBinary(h3, 20) > 0)
	{
		std::string addr;
		GenerateBitcoinAddress(p4, compressed, addr);
		if (checkPrivKey(addr, key, i + 3, compressed))
		{
			nbFoundKey++;
		}
	}
}

void KeyHunt::checkSingleAddress(bool compressed, Int key, int i, Point p1)
{
	unsigned char hash[20];
	secp->GetHash160(compressed, p1, hash);

	if (MatchHash((uint32_t *)hash))
	{
		std::string address;
		GenerateBitcoinAddress(p1, compressed, address);
		if (checkPrivKey(address, key, i, compressed))
		{
			nbFoundKey++;
		}
	}
}

void KeyHunt::checkMultiAddresses(bool compressed, Int key, int i, Point p1)
{
	unsigned char hash[20];
	secp->GetHash160(compressed, p1, hash);

	if (CheckBloomBinary(hash, 20) > 0)
	{
		std::string address;
		GenerateBitcoinAddress(p1, compressed, address);
		if (checkPrivKey(address, key, i, compressed))
		{
			nbFoundKey++;
		}
	}
}

void KeyHunt::checkSingleXPoint(bool compressed, Int key, int i, Point p1)
{
	unsigned char h0[32];
	secp->GetXBytes(compressed, p1, h0);
	if (MatchXPoint((uint32_t *)h0))
	{
		if (checkPrivKeyX(key, i, compressed))
		{
			nbFoundKey++;
		}
	}
}

void KeyHunt::checkMultiXPoints(bool compressed, Int key, int i, Point p1)
{
	unsigned char h0[32];
	secp->GetXBytes(compressed, p1, h0);
	if (CheckBloomBinary(h0, 32) > 0)
	{
		if (checkPrivKeyX(key, i, compressed))
		{
			nbFoundKey++;
		}
	}
}
void KeyHunt::ToggleDebugMode(bool enable, uint64_t updateInterval)
{
	printDebug = enable;
	debugMode = enable;
	if (enable)
	{
		debugUpdateInterval = updateInterval;
		debugInterval = updateInterval;
		printf("Debug mode enabled. Update interval: %lu keys\n", debugUpdateInterval);
	}
	else
	{
		debugUpdateInterval = 0;
		debugInterval = 0;
		printf("Debug mode disabled.\n");
	}
}
void KeyHunt::writeToFile(const std::string &result)
{
	std::ofstream outFile("FOUNDKEY.txt", std::ios::app);
	if (outFile.is_open())
	{
		outFile << result << std::endl;
		outFile.close();
		printf("Result written to FOUNDKEY.txt\n");
	}
	else
	{
		printf("Unable to open file for writing\n");
	}
}
void KeyHunt::output(std::string addr, std::string pAddr, std::string pAddrHex, std::string pubKey)
{
#ifdef WIN64
	WaitForSingleObject(ghMutex, INFINITE);
#else
	pthread_mutex_lock(&ghMutex);
#endif

	std::string result = "PubAddress: " + addr + "\n";
	if (coinType == COIN_BTC)
	{
		result += "Priv (WIF): p2pkh:" + pAddr + "\n";
	}
	result += "Priv (HEX): " + pAddrHex + "\n";
	result += "PubK (HEX): " + pubKey + "\n";
	result += "==========================================\n";

	// Write to file
	writeToFile(result);

	// Display in terminal
	printf("\nMatch found!\n%s", result.c_str());

	// Stop the search
	endOfSearch = true;

#ifdef WIN64
	ReleaseMutex(ghMutex);
#else
	pthread_mutex_unlock(&ghMutex);
#endif
}
