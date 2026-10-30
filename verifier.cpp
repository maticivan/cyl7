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

// Verifies the finite statement of the paper: there is no sign pattern on eleven points with
// properties (P1) and (P2), and no sign pattern on eight points with properties (P1)-(P4).
// Relabelling and reorientation preserve admissibility (see the paper). They are used to 
// reduce the number of signings sigma that are searched.
//
// Points are 0..g_m-1. A signing sigma is normalized when sigma[0][j] == +1 for all j.
// The pairs (a,b) with 1 <= a < b <= g_m-1 are numbered in lexicographic order:
// (1,2) is bit 0, (1,3) is bit 1, and so on. A set bit means sigma[a][b] == -1, a clear bit
// means +1. Code 0 is the signing with all signs +1.
//
 
#include <algorithm>
#include <cassert>
#include <limits>
#include <iostream>
#include <vector>
#include <set>

const int MAXN = 11;                        // the largest number of points the program handles
int g_m = 8;                                // the number of points

int g_pairBit[MAXN][MAXN];                        // g_pairBit[a][b] for 1 <= a < b <= g_m-1

void initPairs() {
    int bit = 0;
    for(int a = 1; a < g_m; ++a){
        for(int b = a + 1; b < g_m; ++b){
            g_pairBit[a][b] = bit;++bit;
        }
    }
}
void decodeSigma(long codeForSigma, int sigma[MAXN][MAXN]) {
    for(int j = 1; j < g_m; ++j){sigma[j][0] = 1; sigma[0][j] = 1;}
    for(int a = 1; a < g_m; ++a){
        for(int b = a + 1; b < g_m; ++b){
            sigma[b][a]=1;
            if((codeForSigma >> g_pairBit[a][b])%2){sigma[b][a]=-1;}
            sigma[a][b]=sigma[b][a];
        }
    }
}
long encodeSigma(const int sigma[MAXN][MAXN]) {
    long codeForSigma = 0;
    for(int j = 1; j < g_m; ++j){assert(sigma[0][j] == +1);}
    for(int a = 1; a < g_m; ++a){
        for(int b = a + 1; b < g_m; ++b){
            if(sigma[a][b] == -1){codeForSigma |= 1L << g_pairBit[a][b];}
        }
    }
    return codeForSigma;
}

// The signing obtained from codeForSigma by the relabelling `permutation`, followed by
// reorientation of every point j with sigma[0][j] == -1, so that the result is normalized
// again. Both operations preserve admissibility (see the paper).
long relabel(long codeForSigma, const int* permutation){ 
    int source[MAXN][MAXN], image[MAXN][MAXN];
    decodeSigma(codeForSigma, source);
    for(int a = 0; a < g_m; ++a){
        for(int b = 0; b < g_m; ++b){
            if (a != b){
                image[a][b] = source[permutation[a]][permutation[b]];
            }
        }
    }
    for(int j = 1; j < g_m; ++j){
        if(image[0][j] == -1){
            for (int m = 0; m < g_m; ++m){
                if (m != j) { image[j][m] = -image[j][m]; image[m][j] = -image[m][j]; }
            }
        }
    }
    return encodeSigma(image);
}

// ---------------------------------------------------------------- canonical code
// Two signings are equivalent if one is obtained from the other by a relabelling followed 
// by renormalization. This is an equivalence relation, and equivalent signings admit the 
// same chi up to the symmetries. The canonical code picks one representative from each 
// class by a fixed rule, so that two signings are equivalent if and only if their canonical 
// codes are equal.
// A three-element set {i,j,k} is odd if sigma[i][j] * sigma[j][k] * sigma[i][k] == -1.
// The invariant of a point i: the sorted list, over the points j != i, of the number of
// points k such that {i,j,k} is odd. A relabelling carries the invariant of a point to
// the invariant of its image. Reorientation does not change which sets are odd, because a
// reorientation flips two of the three signs in every set it touches.
std::vector<int> pointInvariant(const int sigma[MAXN][MAXN], int i) {
    std::vector<int> invariant;
    for(int j = 0; j < g_m; ++j){
        if(j == i){continue;}
        int odd = 0;
        for(int k = 0; k < g_m; ++k){
            if(k != i && k != j && sigma[i][j] * sigma[j][k] * sigma[i][k] == -1){++odd;}
        }
        invariant.push_back(odd);
    }
    std::sort(invariant.begin(), invariant.end());
    return invariant;
}
// The canonical code: the minimum of relabel(code, p) over all permutations p that list the
// points in non-decreasing order of their invariants. The points are first sorted by
// invariant into groups of equal invariant. Then, every order of the points within each group
// is tried. If sigma' = relabel(sigma, q), then the permutations compatible with the
// invariants of sigma' are exactly q composed with those compatible with sigma, so the two
// minima agree. Conversely two signings with the same canonical code are relabellings of
// one signing, hence of each other.
long g_canonicalBest;
void canonicalRecurse(long codeForSigma,
                      int* order,
                      const std::vector<int>& groupEnd,
                      size_t group,
                      int start) {
    if(group == groupEnd.size()){
        g_canonicalBest = std::min(g_canonicalBest, relabel(codeForSigma, order));
        return;
    }
    int end = groupEnd[group];
    std::sort(order + start, order + end);
    do {
        canonicalRecurse(codeForSigma, order, groupEnd, group + 1, end);
    } while(std::next_permutation(order + start, order + end));
}
long canonicalCode(long codeForSigma) {
    int sigma[MAXN][MAXN];
    decodeSigma(codeForSigma, sigma);
    std::vector<std::pair<std::vector<int>, int> > points; // (invariant, point)
    for(int i = 0; i < g_m; ++i){points.push_back({pointInvariant(sigma, i), i});}
    std::sort(points.begin(), points.end());
    int order[MAXN];
    std::vector<int> groupEnd;                             // end of each group of equal invariant
    for(int i = 0; i < g_m; ++i){
        order[i] = points[i].second;
        if((i == g_m - 1) || (points[i].first != points[i + 1].first) ){groupEnd.push_back(i + 1);}
    }
    g_canonicalBest = std::numeric_limits<long>::max();
    canonicalRecurse(codeForSigma, order, groupEnd, 0, 0);
    return g_canonicalBest;
}

// ---------------------------------------------------------------- three-element sets
// The unknowns of the search are the signs chi(a,b,c) with a < b < c, one for each
// three-element set {a,b,c} of points. The set {a,b,c} is represented by the MAXN-bit mask
// (1<<a)|(1<<b)|(1<<c). The 165 three-element sets of MAXN points are numbered 0..164 in
// increasing order of their masks. In this order all sets inside {0,...,m} come before any
// set containing m+1. So the sets inside {0,...,g_m-1} are exactly the first numTriples().

const int MAX_TRIPLES = 165;
int g_tripleIndexOfMask[1 << MAXN];  // 0..164 for a mask with exactly three bits set, otherwise -1
int g_maskOfTripleIndex[MAX_TRIPLES];

int numTriples() { return g_m * (g_m - 1) * (g_m - 2) / 6; }

void initTriples() {
    int index = 0;
    for (int mask = 0; mask < (1 << MAXN); ++mask) {
        int bits = 0;
        for (int i = 0; i < MAXN; ++i) bits += (mask >> i) & 1;
        if (bits == 3) {
            g_tripleIndexOfMask[mask] = index;
            g_maskOfTripleIndex[index] = mask;
            ++index;
        } else {
            g_tripleIndexOfMask[mask] = -1;
        }
    }
    assert(index == MAX_TRIPLES);
}
// Index of the set {a,b,c}; a, b, c distinct, given in any order.
int tripleIndex(int a, int b, int c) {
    return g_tripleIndexOfMask[(1 << a) | (1 << b) | (1 << c)];
}

// g_chi[t] holds chi(a,b,c) for the set number t, with a < b < c. Value 0 means not yet
// assigned.
int g_chi[MAX_TRIPLES];
// The signing currently being searched. Fixed during one call of noAdmissibleChi.
int g_sigma[MAXN][MAXN];
// Whether (P3) and (P4) are checked. They hold for equal radii only; (P1) and (P2) always.
int g_checkP3P4 = 1;
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
// g_p1Instances[t] is the list of instances {a, v1, v2, v3, v4} whose six unknowns
// chi(a,vi,vj) have largest set number t.
std::vector<std::vector<std::vector<int> > > g_p1Instances;

void initP1Instances() {
    g_p1Instances.assign(numTriples(), {});
    for (int a = 0; a < g_m; ++a) {
        for (int v1 = 0; v1 < g_m; ++v1) {
            if (v1 == a) continue;
            for (int v2 = v1 + 1; v2 < g_m; ++v2) {
                if (v2 == a) continue;
                for (int v3 = v2 + 1; v3 < g_m; ++v3) {
                    if (v3 == a) continue;
                    for (int v4 = v3 + 1; v4 < g_m; ++v4) {
                        if (v4 == a) continue;
                        int t = 0;
                        int v[4] = {v1, v2, v3, v4};
                        for (int i = 0; i < 4; ++i)
                            for (int j = i + 1; j < 4; ++j)
                                t = std::max(t, tripleIndex(a, v[i], v[j]));
                        g_p1Instances[t].push_back({a, v1, v2, v3, v4}); 
                    }
                }
            }
        }
    } 
}

// (P1) for one instance: the three signs
//   chi(a,v1,v2) chi(a,v3,v4),   -chi(a,v1,v3) chi(a,v2,v4),   chi(a,v1,v4) chi(a,v2,v3)
// are not all equal. All six unknowns must be assigned.
int threeTermOk(int a, int v1, int v2, int v3, int v4) {
    int s1 =  chiOf(a, v1, v2) * chiOf(a, v3, v4);
    int s2 = -chiOf(a, v1, v3) * chiOf(a, v2, v4);
    int s3 =  chiOf(a, v1, v4) * chiOf(a, v2, v3);
    return !(s1 == s2 && s2 == s3);
}
 
// Returns 1 if every instance of (P1) whose last unknown is t holds for the current chi.
int checkP1(int t) {
    for (size_t k=0;k<g_p1Instances[t].size();++k){
        const std::vector<int>& list = g_p1Instances[t][k];
        if (!threeTermOk(list[0], list[1], list[2], list[3], list[4])){ return 0;}
    }
    return 1;
}
// ---------------------------------------------------------------- (P2)
// An instance of (P2) is a four-element set Q = {a < b < c < d}.
// g_p2Instances[t] holds every Q whose four unknowns have largest set number t. That set
// is {b,c,d}.
std::vector<std::vector<std::vector<int> > > g_p2Instances;

void initP2Instances() {
    g_p2Instances.assign(numTriples(), {});
    for (int a = 0; a < g_m; ++a){
        for (int b = a + 1; b < g_m; ++b){
            for (int c = b + 1; c < g_m; ++c){
                for (int d = c + 1; d < g_m; ++d) {
                    int t = std::max({tripleIndex(b, c, d), tripleIndex(a, c, d),
                                      tripleIndex(a, b, d), tripleIndex(a, b, c)});
                    g_p2Instances[t].push_back({a,b,c,d}); 
                } 
            }
        }
    }
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

// (P2) for one instance Q = {a < b < c < d}. All four unknowns must be assigned.
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

// Returns 1 if every instance of (P2) whose last unknown is t holds for the current chi.
int checkP2(int t) {
    for (size_t k = 0; k < g_p2Instances[t].size(); ++k){
        const std::vector<int>& list = g_p2Instances[t][k];
        if (!fourLineOk(list[0], list[1], list[2], list[3])) return 0;
    }
    return 1;
}

// ---------------------------------------------------------------- (P3), (P4)
// An instance of (P3) or (P4) is a five-element set S = {a < b < c < d < e}.
// g_fiveSetInstances[t] holds every S whose ten unknowns have largest set number t.
std::vector<std::vector<std::vector<int> > > g_fiveSetInstances;

void initFiveSetInstances() {
    g_fiveSetInstances.assign(numTriples(), {});
    for (int a = 0; a < g_m; ++a){
        for (int b = a + 1; b < g_m; ++b){
            for (int c = b + 1; c < g_m; ++c){
                for (int d = c + 1; d < g_m; ++d){
                    for (int e = d + 1; e < g_m; ++e) {
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
                    }
                }
            }
        }
    } 
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
// Returns 1 if every instance of (P3) inside a five-set whose last unknown is t holds.
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
// Property (P4). Let p : {0,1,2,3,4} -> {0,...,g_m-1} be injective and f in {-1,+1}^5.
// They define a sigma' on the pairs of {0,...,4} and a chi' on its triples by
//     sigma'(a,b)   = f[a] f[b]      sigma(p[a],p[b]),
//     chi'(a,b,c)   = f[a] f[b] f[c] chi(p[a],p[b],p[c]).
// (P4) requires that (sigma',chi') never satisfies both conditions (i) and (ii) of the lemma
// on five lines with equal radii (see the paper).
// Exactly 16 pairs (sigma',chi') satisfy both: two choices of s, and two choices for each of
// the three signs that (i) and (ii) leave free.
//
// A pair (sigma',chi') on {0,...,4} is called a five-point pattern below. There are 2^20
// of them. Let E be the set of five-point patterns that violate (P4), that is, the patterns
// which some bijection p of {0,...,4} and some f carry to one of these 16 pairs.
// E has 53760 elements. It is computed once, before the search, by initP4Table.
//
// How E is used. The search assigns the unknowns one at a time. When the unknown t is
// assigned, checkP4(t) is called on the partial assignment chi[0..t], which at that moment
// has already passed checkP1(t), checkP2(t) and checkP3(t). For each five-element subset S
// of the points whose last unknown is t, the restriction of (sigma, chi) to S is read off,
// with S identified with {0,...,4} in increasing order, and looked up in E. If it is in E,
// the branch dies here. If it is not, the branch continues to the unknown t+1, and may die
// later from any of the four checks.
//
// Why a bijection of {0,...,4} is enough, although (P4) quantifies over injective maps
// into {0,...,g_m-1}. An injective p has image some five-set S, and p is the increasing
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
    // The 16 patterns satisfying (i) and (ii) of that lemma.
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

// Returns 1 if no five-set whose last unknown is t carries a pattern excluded by (P4).
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

// Returns 1 if every instance of (P1), (P2), and of (P3), (P4) when g_checkP3P4 is set,
// whose last unknown is t holds for the current chi.
int branchStillAlive(int t) {
    if(!checkP1(t)){return 0;}
    if(!checkP2(t)){return 0;}
    if(!g_checkP3P4){return 1;}
    if(!checkP3(t)){return 0;}
    return checkP4(t);
}
// Depth-first search: assigns the unknowns t, t+1, ..., numTriples()-1 in this order.
// Returns 1 if some completion of the current partial chi passes all checks.
int searchFrom(int t) {
    if (t == numTriples()) return 1;
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
    for(int t = 0; t < numTriples(); ++t){g_chi[t] = 0;}
    return !searchFrom(0);
}
// The signings on m+1 points obtained from the signings in `codes`, given for m points, by
// adding the point m with sigma[0][m] = +1 and every choice of the signs sigma[j][m],
// 1 <= j <= m-1. Sets g_m = m+1 and renumbers the pairs accordingly.
std::vector<long> extendByOnePoint(const std::vector<long>& codes, int m) {
    std::vector<long> result;
    for(size_t c = 0; c < codes.size(); ++c){
        int sigma[MAXN][MAXN];
        g_m = m;
        initPairs();
        decodeSigma(codes[c], sigma);
        g_m = m + 1;
        initPairs();
        for(long choice = 0; choice < (1L << (m - 1)); ++choice){
            sigma[0][m] = 1;
            sigma[m][0] = 1;
            for(int j = 1; j < m; ++j){
                int sign = ((choice >> (j - 1)) % 2) ? -1 : 1;
                sigma[j][m] = sign;
                sigma[m][j] = sign;
            }
            result.push_back(encodeSigma(sigma));
        }
    }
    return result;
}
// No admissible sign pattern on n points. Returns 1 if verified.
// Level m holds one signing from each class (under relabelling and reorientation) of
// signings on m points that admit an admissible chi. The candidates for level m+1 are the
// extensions of the signings of level m. A candidate is skipped if a candidate with the same
// canonical code was searched before. Every admissible pattern on m+1 points restricts to
// one on m points, so no class is lost. The statement is verified if level n is empty.
int noAdmissiblePattern(int n) {
    std::vector<long> level(1, 0);             // the one signing on two points
    for(int m = 3; m <= n; ++m){
        std::vector<long> candidates = extendByOnePoint(level, m - 1);    // now g_m == m
        initP1Instances();
        initP2Instances();
        initFiveSetInstances();
        std::set<long> seen;                   // canonical codes of the signings searched
        std::vector<long> nextLevel;
        for(size_t c = 0; c < candidates.size(); ++c){
            long codeForSigma = candidates[c];
            if(!seen.insert(canonicalCode(codeForSigma)).second){continue;}
            if(!noAdmissibleChi(codeForSigma)){nextLevel.push_back(codeForSigma);}
        }
        std::cout << (m < 10 ? " " : "") << m << " points: "
                  << (nextLevel.size() < 10 ? " " : "") << nextLevel.size() << " survive\n";
        level = nextLevel;
    }
    return level.empty();
}
void printExplanation(int n, const char* properties, const char* pairs, const char* years) {
    std::cout << "Computer-assisted proof that for n = " << n << " no (sigma, chi) with\n"
              << "sigma in {-1,+1}^C(" << n << ",2) and chi in {-1,+1}^C(" << n << ",3) satisfies " << properties << ".\n\n"
              << "Brute force is impossible: there are " << pairs << " pairs (sigma, chi).\n"
              << "At 10^9 per second this would take about " << years << " years.\n\n"
              << "The proof proceeds by the number of points m = 3, 4, ..., " << n << ". At each m the\n"
              << "program examines assignments sigma to the C(m,2) pairs of the points 0..m-1.\n"
              << "For each sigma it searches all assignments chi to the C(m,3) three-element\n"
              << "subsets for one that satisfies " << properties << " on these m points. If none\n"
              << "exists, sigma is eliminated. Only the sigma whose restriction to the first\n"
              << "m-1 points survived the previous stage are examined. This loses nothing: if\n"
              << "(sigma, chi) satisfies " << properties << " on m points, so does its restriction to\n"
              << "the first m-1 points. Assignments that differ by a relabelling of the points\n"
              << "or by reorientations are examined only once.\n\n";
}
int main() {
    initTriples();
    initP4Table();
    std::cout << "Part 1. ";
    printExplanation(11, "(P1) and (P2)", "2^220, about 10^66", "10^50");
    g_checkP3P4 = 0;
    int a = noAdmissiblePattern(11);
    std::cout << "\nPart 1 is " << (a ? "proved" : "NOT proved") << ".\n\n";
    std::cout << "Part 2. ";
    printExplanation(8, "(P1), (P2), (P3), and (P4)", "2^84, about 10^25", "10^9");
    g_checkP3P4 = 1;
    int b = noAdmissiblePattern(8);
    std::cout << "\nPart 2 is " << (b ? "proved" : "NOT proved") << ".\n";
    return 0;
}
