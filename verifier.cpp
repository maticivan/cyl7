//*************************************************************************************************
//*************************************************************************************************
//* The MIT License (MIT)                                                                         *
//* Copyright (C) 2026                                                                            *
//* Kenta Kitamura, Ivan Matic, Rados Radoicic, and Andreas Spomer                                *
//*                                                                                               *
//* Permission is hereby granted, free of charge, to any person obtaining a copy of this          *
//* software and associated documentation files (the "Software"), to deal in the Software         *
//* without restriction, including without limitation the rights to use, copy, modify, merge,     *
//* publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons    *
//* to whom the Software is furnished to do so, subject to the following conditions:              *
//*                                                                                               *
//* The above copyright notice and this permission notice shall be included in all copies or      *
//* substantial portions of the Software.                                                         *
//*                                                                                               *
//* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED,           *
//* INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR      *
//* PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE     *
//* FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR          *
//* OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER        *
//* DEALINGS IN THE SOFTWARE.                                                                     *
//*************************************************************************************************

// Verifies that there is no admissible sign pattern on eight points (the finite statement of the paper:
// properties (P1)-(P4) of Definition "admissible sign pattern"). Relabelling and reorientation
// (the symmetry lemma) are used to reduce the number of signings sigma that are searched.
//
// Points are 0..7. A signing sigma is normalized when sigma[0][j] == +1 for all j.
// The 21 pairs (a,b) with 1 <= a < b <= 7 are numbered in lexicographic order:
// (1,2) is bit 0, (1,3) is bit 1, ..., (1,7) is bit 5, (2,3) is bit 6, ..., (6,7) is bit 20.
// A set bit means sigma[a][b] == -1, a clear bit means +1.
// Code 0 is the homogeneous signing, all +1.
//
 
#include <algorithm>
#include <cassert>
#include <iostream>
#include <vector>

const long NUM_SIGMAS = 1L << 21;
const long NUM_PERMUTATIONS  = 40320;

int g_pairBit[8][8];                        // g_pairBit[a][b] for 1 <= a < b <= 7
std::vector<std::vector<int>> g_allPermutations;      // all permutations of 0..7; g_allPermutations[0] is the identity

void initPairsAndPermutations() {
    int bit = 0;
    for(int a = 1; a < 8; ++a){
        for(int b = a + 1; b < 8; ++b){
            g_pairBit[a][b] = bit;++bit;
        }
    }
    std::vector<int> p = {0, 1, 2, 3, 4, 5, 6, 7};
    do g_allPermutations.push_back(p); while (std::next_permutation(p.begin(), p.end()));
    assert((long)g_allPermutations.size() == NUM_PERMUTATIONS);
}
void decodeSigma(long codeForSigma, int sigma[8][8]) {
    for(int j = 1; j < 8; ++j){sigma[j][0] = 1; sigma[0][j] = 1;}
    for(int a = 1; a < 8; ++a){
        for(int b = a + 1; b < 8; ++b){
            sigma[b][a]=1;
            if((codeForSigma >> g_pairBit[a][b])%2){sigma[b][a]=-1;}
            sigma[a][b]=sigma[b][a];
        }
    }
}
long encodeSigma(const int sigma[8][8]) {
    long codeForSigma = 0;
    for(int j = 1; j < 8; ++j){assert(sigma[0][j] == +1);}
    for(int a = 1; a < 8; ++a){
        for(int b = a + 1; b < 8; ++b){
            if(sigma[a][b] == -1){codeForSigma |= 1L << g_pairBit[a][b];}
        }
    }
    return codeForSigma;
}

// The signing obtained from codeForSigma by the relabelling `permutation`, followed by
// reorientation of every point j with sigma[0][j] == -1, so that the result is normalized
// again. Both operations preserve admissibility (symmetry lemma, parts (a) and (b)).
long relabel(long codeForSigma, const std::vector<int>& permutation) {
    int source[8][8], image[8][8];
    decodeSigma(codeForSigma, source);
    for(int a = 0; a < 8; ++a){
        for(int b = 0; b < 8; ++b){
            if (a != b){
                image[a][b] = source[permutation[a]][permutation[b]];
            }
        }
    }
    for(int j = 1; j < 8; ++j){
        if(image[0][j] == -1){
            for (int m = 0; m < 8; ++m){
                if (m != j) { image[j][m] = -image[j][m]; image[m][j] = -image[m][j]; }
            }
        }
    }
    return encodeSigma(image);
}


// ---------------------------------------------------------------- triples
// A triple {a,b,c} of points is represented by the 8-bit mask (1<<a)|(1<<b)|(1<<c).
// The 56 triples are numbered 0..55 in increasing order of their masks.
// In this order all triples inside {0,...,m} come before any triple containing m+1.

int g_tripleIndexOfMask[256];     // 0..55 for a mask with exactly three bits set, otherwise -1
int g_maskOfTripleIndex[56];

void initTriples() {
    int index = 0;
    for (int mask = 0; mask < 256; ++mask) {
        int bits = 0;
        for (int i = 0; i < 8; ++i) bits += (mask >> i) & 1;
        if (bits == 3) {
            g_tripleIndexOfMask[mask] = index;
            g_maskOfTripleIndex[index] = mask;
            ++index;
        } else {
            g_tripleIndexOfMask[mask] = -1;
        }
    }
    assert(index == 56);
}
// Index of the triple {a,b,c}; a, b, c distinct, in any order.
int tripleIndex(int a, int b, int c) {
    return g_tripleIndexOfMask[(1 << a) | (1 << b) | (1 << c)];
}

// g_chi[t] holds the value of chi on the triple t, in increasing order of its elements.
// Value 0 means not yet assigned.
int g_chi[56];
// The signing currently being searched. Fixed during one call of noAdmissibleChi.
int g_sigma[8][8];
// chi(a,b,c) for distinct a, b, c in any order: the stored value times the sign of the
// permutation that sorts (a,b,c).
int chiOf(int a, int b, int c) {
    int sign = 1;
    if (a > b) { std::swap(a, b); sign = -sign; }
    if (b > c) { std::swap(b, c); sign = -sign; }
    if (a > b) { std::swap(a, b); sign = -sign; }
    return sign * g_chi[g_tripleIndexOfMask[(1 << a) | (1 << b) | (1 << c)]];
}
// ---------------------------------------------------------------- (P1)
// An instance of (P1) is a point a and four other points v1 < v2 < v3 < v4.
// g_p1Instances[t] is the list of instances {a, v1, v2, v3, v4} whose six triples
// {a,vi,vj} have largest index t.
std::vector<std::vector<std::vector<int> > > g_p1Instances(56);

void initP1Instances() {
    int total = 0;
    for (int a = 0; a < 8; ++a) {
        for (int v1 = 0; v1 < 8; ++v1) {
            if (v1 == a) continue;
            for (int v2 = v1 + 1; v2 < 8; ++v2) {
                if (v2 == a) continue;
                for (int v3 = v2 + 1; v3 < 8; ++v3) {
                    if (v3 == a) continue;
                    for (int v4 = v3 + 1; v4 < 8; ++v4) {
                        if (v4 == a) continue;
                        int t = 0;
                        int v[4] = {v1, v2, v3, v4};
                        for (int i = 0; i < 4; ++i)
                            for (int j = i + 1; j < 4; ++j)
                                t = std::max(t, tripleIndex(a, v[i], v[j]));
                        g_p1Instances[t].push_back({a, v1, v2, v3, v4});
                        ++total;
                    }
                }
            }
        }
    }
    assert(total == 280);
}

// (P1) for one instance: the three signs
//   chi(a,v1,v2) chi(a,v3,v4),   -chi(a,v1,v3) chi(a,v2,v4),   chi(a,v1,v4) chi(a,v2,v3)
// are not all equal. All six triples must be assigned.
int threeTermOk(int a, int v1, int v2, int v3, int v4) {
    int s1 =  chiOf(a, v1, v2) * chiOf(a, v3, v4);
    int s2 = -chiOf(a, v1, v3) * chiOf(a, v2, v4);
    int s3 =  chiOf(a, v1, v4) * chiOf(a, v2, v3);
    return !(s1 == s2 && s2 == s3);
}
 
// Returns 1 if every instance of (P1) whose last triple is t holds for the current chi.
int checkP1(int t) {
    for (size_t k=0;k<g_p1Instances[t].size();++k){
        const std::vector<int>& list = g_p1Instances[t][k];
        if (!threeTermOk(list[0], list[1], list[2], list[3], list[4])){ return 0;}
    }
    return 1;
}
// ---------------------------------------------------------------- (P2)
// An instance of (P2) is a four-element set Q = {a < b < c < d}.
// g_p2Instances[t] holds every Q whose four triples have
// largest index t. That triple is {b,c,d}.
std::vector<std::vector<std::vector<int> > > g_p2Instances(56);

void initP2Instances() {
    int total = 0;
    for (int a = 0; a < 8; ++a)
        for (int b = a + 1; b < 8; ++b)
            for (int c = b + 1; c < 8; ++c)
                for (int d = c + 1; d < 8; ++d) {
                    int t = std::max({tripleIndex(b, c, d), tripleIndex(a, c, d),
                                      tripleIndex(a, b, d), tripleIndex(a, b, c)});
                    g_p2Instances[t].push_back({a,b,c,d});
                    ++total;
                }
    assert(total == 70);
}
// Whether two pairs of points have a common element.
int sharePoint(int pair[2][2]) {
    return pair[0][0] == pair[1][0] || pair[0][0] == pair[1][1]
        || pair[0][1] == pair[1][0] || pair[0][1] == pair[1][1];
}

// kappa^Q for Q = {q[0] < q[1] < q[2] < q[3]}, as defined before (P1)-(P4) in the paper.
// Output in kappa[0..3].
void kappaOf(const int q[4], int kappa[4]) {
    kappa[0] =  chiOf(q[1], q[2], q[3]);
    kappa[1] = -chiOf(q[0], q[2], q[3]);
    kappa[2] =  chiOf(q[0], q[1], q[3]);
    kappa[3] = -chiOf(q[0], q[1], q[2]);
}

// (P2) for one instance Q = {a < b < c < d}. All four triples must be assigned.
// P is the set of pairs (i,j) in Q with
// sigma_ij kappa_i kappa_j = +1. Allowed: |P| = 3; |P| = 2 with the two pairs sharing
// a point; |P| = 4 with the two pairs outside P sharing a point.
int fourLineOk(int a, int b, int c, int d) {
    int q[4] = {a, b, c, d};
    int kappa[4];
    kappaOf(q,kappa);
    int numPlus = 0;
    int plusPair[2][2], minusPair[2][2];      // the first two pairs of each kind
    int numMinus = 0;
    for (int i = 0; i < 4; ++i)
        for (int j = i + 1; j < 4; ++j) {
            if (g_sigma[q[i]][q[j]] * kappa[i] * kappa[j] == +1) {
                if (numPlus < 2) { plusPair[numPlus][0] = i; plusPair[numPlus][1] = j; }
                ++numPlus;
            } else {
                if (numMinus < 2) { minusPair[numMinus][0] = i; minusPair[numMinus][1] = j; }
                ++numMinus;
            }
        }
    if (numPlus == 3) return 1;
    if (numPlus == 2) return sharePoint(plusPair);
    if (numPlus == 4) return sharePoint(minusPair);
    return 0;
}

// Returns 1 if every instance of (P2) whose last triple is t holds for the current chi.
int checkP2(int t) {
    for (size_t k = 0; k < g_p2Instances[t].size(); ++k){
        const std::vector<int>& list = g_p2Instances[t][k];
        if (!fourLineOk(list[0], list[1], list[2], list[3])) return 0;
    }
    return 1;
}

// ---------------------------------------------------------------- (P3), (P4)
// An instance of (P3) or (P4) is a five-element set S = {a < b < c < d < e}.
// g_fiveSetInstances[t] holds every S whose ten triples have largest index t.
std::vector<std::vector<std::vector<int> > > g_fiveSetInstances(56);

void initFiveSetInstances() {
    int total = 0;
    for (int a = 0; a < 8; ++a){
        for (int b = a + 1; b < 8; ++b){
            for (int c = b + 1; c < 8; ++c){
                for (int d = c + 1; d < 8; ++d){
                    for (int e = d + 1; e < 8; ++e) {
                        int s[5] = {a, b, c, d, e};
                        int t = 0;
                        for (int i = 0; i < 5; ++i){
                            for (int j = i + 1; j < 5; ++j){
                                for (int k = j + 1; k < 5; ++k){
                                    t = std::max(t, tripleIndex(s[i], s[j], s[k]));
                                }
                            }
                        }
                        g_fiveSetInstances[t].push_back({a, b, c, d, e});
                        ++total;
                    }
                }
            }
        }
    }
    assert(total == 56);
}

// (P3) for one pair I, J of four-element sets, both sorted. For each g in {-1,+1}
// there must be j in J such that at least two i in I \ {j} have
// sigma_ji kappa^J_j kappa^I_i = g.
int p3Ok(const int I[4], const int J[4]) {
    int kI[4], kJ[4];
    kappaOf(I, kI);
    kappaOf(J, kJ);
    for (int g = -1; g <= 1; g += 2) {
        int found = 0;
        for (int y = 0; y < 4 && !found; ++y) {
            int j = J[y];
            int count = 0;
            for (int x = 0; x < 4; ++x) {
                int i = I[x];
                if ( (i != j) && (g_sigma[j][i] * kJ[y] * kI[x] == g) ){++count;}
            }
            if(count >= 2){found = 1;}
        }
        if (!found) return 0;
    }
    return 1;
}
// Returns 1 if every instance of (P3) inside a five-set whose last triple is t holds.
int checkP3(int t) {
    for (size_t k = 0; k < g_fiveSetInstances[t].size(); ++k) {
        const std::vector<int>& s = g_fiveSetInstances[t][k];
        int sub[5][4];                       // sub[m] = S without s[m], sorted
        for (int m = 0; m < 5; ++m) {
            int n = 0;
            for (int i = 0; i < 5; ++i){
                if (i != m){sub[m][n++] = s[i];}
            }
        }
        for (int mI = 0; mI < 5; ++mI){
            for (int mJ = 0; mJ < 5; ++mJ){
                if (!p3Ok(sub[mI], sub[mJ])){return 0;}
            }
        }
    }
    return 1;
}

// ---------------------------------------------------------------- (P4)
//
// Property (P4). Let p : {0,1,2,3,4} -> {0,...,7} be injective and f in {-1,+1}^5.
// They define a sigma' on the pairs of {0,...,4} and a chi' on its triples by
//     sigma'(a,b)   = f[a] f[b]      sigma(p[a],p[b]),
//     chi'(a,b,c)   = f[a] f[b] f[c] chi(p[a],p[b],p[c]).
// (P4) requires that (sigma',chi') never satisfies both (i) and (ii) of the five-line lemma.
// Exactly 16 pairs (sigma',chi') satisfy both: two choices of s, and two choices for each of
// the three signs that (i) and (ii) leave free.
//
// A pair (sigma',chi') on {0,...,4} is called a five-point pattern below. There are 2^20
// of them. Let E be the set of five-point patterns that violate (P4), that is, the patterns
// which some bijection p of {0,...,4} and some f carry to one of these 16 pairs.
// E has 53760 elements. It is computed once, before the search, by initP4Table.
//
// How E is used. The search assigns the triples one at a time. When the triple t is
// assigned, checkP4(t) is called on the partial assignment chi[0..t], which at that moment
// has already passed checkP1(t), checkP2(t) and checkP3(t). For each five-element subset S
// of {0,...,7} whose last triple is t, the restriction of (sigma, chi) to S is read off,
// with S identified with {0,...,4} in increasing order, and looked up in E. If it is in E,
// the branch dies here. If it is not, the branch continues to the triple t+1, and may die
// later from any of the four checks.
//
// Why a bijection of {0,...,4} is enough, although (P4) quantifies over injective maps
// into {0,...,7}. An injective p has image some five-set S, and p is the increasing
// identification of S with {0,...,4} followed by a bijection of {0,...,4}. So (sigma',chi')
// is obtained from the restriction to S by a bijection and an f. Hence (P4) holds for all
// p and f if and only if no restriction to a five-set lies in E.
//
// Encoding. A five-point pattern is stored in 20 bits: bits 0..9 hold sigma' on the 10
// pairs, in the order of g_pair5; bits 10..19 hold chi' on the 10 sorted triples, in the
// order of g_triple5. A set bit means +1, a clear bit means -1.

int g_pair5[5][5];            // index 0..9 of the pair {a,b}, a < b
int g_triple5[5][5][5];       // index 0..9 of the triple {a,b,c}, a < b < c
std::vector<char> g_isP4Pattern;   // indexed by the 20-bit encoding; 1 if the pattern is in E 

int sigma5(int pattern, int a, int b) {           // a != b
    if (a > b) std::swap(a, b);
    return ((pattern >> g_pair5[a][b]) & 1) ? +1 : -1;
}
int chi5(int pattern, int a, int b, int c) {      // distinct, any order
    int sign = 1;
    if (a > b) { std::swap(a, b); sign = -sign; }
    if (b > c) { std::swap(b, c); sign = -sign; }
    if (a > b) { std::swap(a, b); sign = -sign; }
    return sign * (((pattern >> (10 + g_triple5[a][b][c])) & 1) ? +1 : -1);
}
int encode5(const int sigma[5][5], const int chi[5][5][5]) {   // chi given on sorted triples
    int pattern = 0;
    for(int a = 0; a < 5; ++a){
        for(int b = a + 1; b < 5; ++b){
            if(sigma[a][b] == +1){pattern |= 1 << g_pair5[a][b];}
        }
    }
    for(int a = 0; a < 5; ++a){
        for(int b = a + 1; b < 5; ++b){
            for(int c = b + 1; c < 5; ++c){
                if(chi[a][b][c] == +1){pattern |= 1 << (10 + g_triple5[a][b][c]);}
            }
        }
    }
    return pattern;
}

// The pattern obtained from `pattern` by relabelling with p and reorienting with f:
// sigma'(a,b) = f[a] f[b] sigma(p[a],p[b]),  chi'(a,b,c) = f[a] f[b] f[c] chi(p[a],p[b],p[c]).
int transport5(int pattern, const int p[5], const int f[5]) {
    int sigma[5][5] = {};
    int chi[5][5][5] = {};
    for(int a = 0; a < 5; ++a){
        for(int b = a + 1; b < 5; ++b){
            sigma[a][b] = f[a] * f[b] * sigma5(pattern, p[a], p[b]);
        }
    }
    for(int a = 0; a < 5; ++a){
        for(int b = a + 1; b < 5; ++b){
            for (int c = b + 1; c < 5; ++c){
                chi[a][b][c] = f[a] * f[b] * f[c] * chi5(pattern, p[a], p[b], p[c]);
            }
        }
    }
    return encode5(sigma, chi);
}

void initP4Table() {
    int k = 0;
    for(int a = 0; a < 5; ++a){
        for(int b = a + 1; b < 5; ++b){
            g_pair5[a][b] = k++;
        }
    }
    k = 0;
    for(int a = 0; a < 5; ++a){
        for(int b = a + 1; b < 5; ++b){
            for(int c = b + 1; c < 5; ++c){
                g_triple5[a][b][c] = k++;
            }
        }
    }
    g_isP4Pattern.assign(1 << 20, 0);
    // The 16 patterns satisfying (i) and (ii) of the five-line lemma.
    std::vector<int> toDo;
    for(int s = -1; s <= 1; s += 2){
        for(int x024 = -1; x024 <= 1; x024 += 2){
            for(int x234 = -1; x234 <= 1; x234 += 2){                
                for(int s34 = -1; s34 <= 1; s34 += 2){
                    int sigma[5][5] = {}; 
                    int chi[5][5][5] = {};
                    chi[0][1][2] = +1; 
                    chi[0][1][3] = +1; 
                    chi[0][1][4] = +1; 
                    chi[1][2][3] = +1; 
                    chi[1][2][4] = +1;
                    chi[0][2][3] = -1; 
                    chi[0][3][4] = -1; 
                    chi[1][3][4] = -1;
                    chi[0][2][4] = x024; 
                    chi[2][3][4] = x234;
                    for(int a = 0; a < 5; ++a){
                        for(int b = a + 1; b < 5; ++b){
                            sigma[a][b] = s;
                        }
                    }
                    sigma[0][3] = -s; sigma[3][4] = s34;
                    int pattern = encode5(sigma, chi);
                    if(!g_isP4Pattern[pattern]){ 
                        g_isP4Pattern[pattern] = 1; 
                        toDo.push_back(pattern); 
                    }
                }
            }
        }
    }
    // Close under relabelling and reorientation. Generators: a transposition, a 5-cycle,
    // and the reorientation of point 0.
    const int gp[3][5] = {{1,0,2,3,4}, {1,2,3,4,0}, {0,1,2,3,4}};
    const int gf[3][5] = {{1,1,1,1,1}, {1,1,1,1,1}, {-1,1,1,1,1}};
    while(!toDo.empty()){
        int pattern = toDo.back(); toDo.pop_back();
        for(int g = 0; g < 3; ++g){
            int image = transport5(pattern, gp[g], gf[g]);
            if (!g_isP4Pattern[image]) { g_isP4Pattern[image] = 1; toDo.push_back(image); }
        }
    }
    long total = 0; 
    for(size_t i = 0; i < g_isP4Pattern.size(); ++i){
        total += g_isP4Pattern[i];
    }
    assert(total == 53760);
}

// Returns 1 if no five-set whose last triple is t carries a pattern excluded by (P4).
int checkP4(int t) {
    for (size_t k = 0; k < g_fiveSetInstances[t].size(); ++k) {
        const std::vector<int>& s = g_fiveSetInstances[t][k];
        int sigma[5][5] = {}, chi[5][5][5] = {};
        for (int a = 0; a < 5; ++a) for (int b = a + 1; b < 5; ++b)
            sigma[a][b] = g_sigma[s[a]][s[b]];
        for (int a = 0; a < 5; ++a) for (int b = a + 1; b < 5; ++b) for (int c = b + 1; c < 5; ++c)
            chi[a][b][c] = chiOf(s[a], s[b], s[c]);
        if (g_isP4Pattern[encode5(sigma, chi)]) return 0;
    }
    return 1;
}


// Returns 1 if every instance of (P1)-(P4) whose last triple is t holds for the current chi.
int branchStillAlive(int t) {
    if(!checkP1(t)){return 0;}
    if(!checkP2(t)){return 0;}
    if(!checkP3(t)){return 0;}
    return checkP4(t);
}
// Depth-first search: assigns chi on triples t, t+1, ..., 55 in this order.
// Returns 1 if some completion of the current partial chi passes all checks.
int searchFrom(int t) {
    if (t == 56) return 1;
    for (int value = -1; value <= 1; value += 2) {
        g_chi[t] = value;
        if(branchStillAlive(t) && searchFrom(t + 1)){return 1;}
    }
    g_chi[t] = 0;
    return 0;
}
// Returns 1 if no chi makes (sigma, chi) admissible.
int noAdmissibleChi(long codeForSigma) {
    decodeSigma(codeForSigma, g_sigma);
    for(int t = 0; t < 56; ++t){g_chi[t] = 0;}
    return !searchFrom(0);
}
// No admissible sign pattern on eight points. Returns 1 if verified.
int noAdmissiblePatternOn8Points() {
    std::vector<bool> covered(NUM_SIGMAS);
    long numCovered = 0;
    int noCounterexample = 1;
    long codeForSigma=0;
    while(noCounterexample && codeForSigma < NUM_SIGMAS){
        if (!covered[codeForSigma]){
            noCounterexample = noAdmissibleChi(codeForSigma);
            if(noCounterexample){
                for(long perm = 0; perm < NUM_PERMUTATIONS; ++perm){
                    long sigmaImage = relabel(codeForSigma, g_allPermutations[perm]);
                    assert(0 <= sigmaImage && sigmaImage < NUM_SIGMAS);
                    if (!covered[sigmaImage]) { covered[sigmaImage] = true; ++numCovered; }
                }
            }
        }
        ++codeForSigma;
    }
    if (numCovered != NUM_SIGMAS) return 0;
    return noCounterexample;
}
int main() {
    initPairsAndPermutations();
    initTriples();
    initP1Instances();
    initP2Instances();
    initFiveSetInstances();
    initP4Table(); 
    std::cout << noAdmissiblePatternOn8Points() << "\n";
    return 0;
}
