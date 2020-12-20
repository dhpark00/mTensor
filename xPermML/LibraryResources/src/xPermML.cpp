/*********************************************************************
   xPermML.cpp (2014.04, 2018.11, 2020.12) using C++17

   based on xperm.c 1.2.3 (23 August 2015)
 *********************************************************************/

#include "xPermML.h"

/*********************************************************************/
/********************** canonical_perm_ext ***************************/
/*********************************************************************/

perm_t NULL_Imag;

// returns v1 - v2
vec_t complement_vec(const vec_t& v1, const vec_t& v2) {
    vec_t v;
    for (auto k : v1)
        if (!memberq_vec(v2, k)) v.push_back(k);

    return v;
}

// NB: the returned elements keep the original order in v1
vec_t intersection_vec(const vec_t& v1, const vec_t& v2) {
    vec_t v;
    for (auto k : v1)
        if (memberq_vec(v2, k) && !memberq_vec(v, k)) v.push_back(k);

    return v;
}

vec_t join_vec(vec_t v1, vec_t v2) {  // pass by value
    vec_t v{ std::move(v1) };
    std::move(v2.begin(), v2.end(), std::back_inserter(v));
    return v;
}

/* finds the position of 'k' in vec, or else gives 0 if k is not in vec.
 * Note that it starts from the end so that
 * if k appears several times in vec it will only find the last one. */
size_t position_vec(const vec_t& vec, size_t k) {
    size_t n{ vec.size() };

    while (n--)
        if (vec[n] == k) return n + 1;

    return 0;
}

vec_t range_vec(size_t n) {
    vec_t v(n);
    for (size_t i = 0; i < n; ++i) v[i] = i + 1;
    return v;
}

vec_t sort_vec(vec_t vec) {  // pass by value
    vec_t v{ std::move(vec) };
    std::sort(v.begin(), v.end());
    return v;
}

vec_t take_vec(const vec_t& vec, size_t k) {
    if (k >= vec.size()) return vec;
    vec_t v(vec.begin(), vec.begin() + k);
    return v;  // NRVO: Beginning C++17 (2018), page 681
}

/*********************************************************************/

// product in Imag notation
void operator *=(perm_t& lhs, const perm_t& rhs) {
    for (size_t i = 0; i < lhs.size(); ++i)
        lhs[i] = rhs[lhs[i] - 1];
}

const perm_t operator *(perm_t v1, const perm_t& v2) {  // pass by value
    perm_t v{ std::move(v1) };
    v *= v2;
    return v;
}

/*********************************************************************/

perm_t inverse_perm(const perm_t& vec) {
    perm_t v(vec.size());
    for (size_t i = 0; i < vec.size(); i++)
        v[vec[i] - 1] = i + 1;
    return v;
}

// image of point under the permutation
size_t onpoint(size_t point, const perm_t& perm) {
    if (point > 0 && point <= perm.size())
        return perm[point - 1];
    else
        return point;
}

vec_t  onpoints(const perm_t& lst, const perm_t& perm) {
    vec_t v(lst.size());
    std::transform(lst.begin(), lst.end(), v.begin(),
                   [&perm](size_t k) { return onpoint(k, perm); });
    return v;
}

// sorts lst according to the order given by B
perm_t sortB(const perm_t& lst, const vec_t& B) {
    if (lst.size() == 0) return lst;

    // elements of list in B, keeping order of B, moved to dest
    perm_t dest{ intersection_vec(B, lst) };

    // other elements of lst are appended to dest
    perm_t v{ sort_vec(complement_vec(lst, B)) };
    std::move(v.begin(), v.end(), std::back_inserter(dest));

    return dest;
}

/*********************************************************************/

/* orbit of a given point under a GS. */
perm_t orbit(size_t point, const gs_t& GS) {
    perm_t orb{ point };

    size_t np{ 0 };  // index of current element in the orb
    while (np < orb.size()) {
        for (const auto& perm : GS) {
            size_t gamma{ onpoint(orb[np], perm) };
            if (!memberq_vec(orb, gamma)) orb.push_back(gamma);
        }
        np++;
    }
    return orb;
}

/* all orbits of GS (with n-permutations).
 * Note that we use a very special notation: the result is a vector orbits of length n
 * such that all points marked with 1 belong to the same orbit;
 * all points marked with 2 belong to another orbit, and so on. */
perm_t all_orbits(const gs_t& GS, size_t n) {
    perm_t dest(n, 0);  // initialize orbits

    // compute orbits
    size_t oidx{ 1 };  // orbit index
    for (size_t i = 1; i <= n; ++i) {
        if (dest[i - 1] == 0) {  // new orbit condition
            perm_t orb{ orbit(i, GS) };  // compute new orbit

            // mark points of new orbit with index oidx
            for (size_t j = 0; j < orb.size(); j++) dest[orb[j] - 1] = oidx;

            oidx++;  // increment index for next orbit
        }
    }

    return dest;
}

/* Orbit of point under the GeneratingSet GS with n-permutations.
 * The result is stored in the vectors nu of permutations and
 * w of backward points. If init=true both nu and w are reset to 0. */
perm_t schreier_orbit(size_t point, const gs_t& GS, size_t n, gs_t& nu, perm_t& w, bool init) {
    // initialize schreier with zeros if required
    if (init) { nu.assign(n, perm_t(n, 0)); w.assign(n, 0); }

    // first element of orbit. There is no backward pointer
    perm_t orb{ point };

    // other elements of orbit
    size_t np{ 0 }; // index of current element in the orbit
    while (np < orb.size()) {
        for (const auto& perm : GS) {
            size_t gamma{ onpoint(orb[np], perm) };  // orb[np] == oldgamma
            if (!memberq_vec(orb, gamma)) {
                orb.push_back(gamma);    // append to orbit
                nu[gamma - 1] = perm;    // perm moving oldgamma to gamma
                w[gamma - 1] = orb[np]; // backward pointer of newgamma
            }
        }
        np++;
    }

    return orb;
}

/* All orbits of a given GS with n-permutations,
 * with combined vectors of backward permutations and pointers.
 * Note that we do not return the orbits information,
 * though it can be reconstructed from w and nu. */
void schreier_vector(gs_t& nu, perm_t& w, size_t point, const gs_t& GS, size_t n) {
    // first orbit
    perm_t orb{ schreier_orbit(point, GS, n, nu, w, true) };  // initialize nu and w

    // other orbits
    perm_t usedpoints{ orb };
    for (size_t i = 1; i <= n; ++i) {
        if (!memberq_vec(usedpoints, i)) {
            orb = schreier_orbit(i, GS, n, nu, w, false);
            std::copy(orb.begin(), orb.end(), std::back_inserter(usedpoints));
        }
    }
}

/* traces the Schreier vector (orbits, nu, w) with the point given,
 * returning a permutation wich moves the first
 * point of the corresponding orbit to point.
 * If n <= 0 or point > n, return NULL_Imag. */
perm_t trace_schreier(size_t point, const gs_t& nu, const perm_t& w) {
    size_t n{ w.size() };
    if (n <= 0 || point > n) return NULL_Imag;  // assert(p <= n)

    perm_t perm;
    if (w[point - 1] == 0)
        perm = range_vec(n);
    else
        perm = trace_schreier(w[point - 1], nu, w) * nu[point - 1];

    return perm;
}

/*********************************************************************/

/* the permutations that stabilize the points among the GS */
gs_t stabilizer(const perm_t& points, const gs_t& GS) {
    gs_t subGS; bool stable;
    for (const auto& perm : GS) {
        stable = true;
        for (size_t i = 0; i < points.size(); ++i) {
            if (onpoint(points[i], perm) != points[i]) {
                stable = false; break;
            }
        }
        if (stable) subGS.push_back(perm);
    }
    return subGS;
}

/* a canonical representant of a n-permutation
 * in the group described by a SGS (base,GS).
 * The free slots are different at return time. */
perm_t right_coset_rep(const perm_t& perm, size_t n,
    const perm_t& base, const gs_t& GS, perm_t& freeps) {
    // trivial case without symmetries
    if (GS.size() == 0) return perm;

    // initialize cr_perm and gs
    perm_t cr_perm{ perm }; gs_t gs{ GS };

    // loop over elements of base
    gs_t nu; perm_t w;
    for (const auto& bi : base) {
        vec_t delta1{ intersection_vec(schreier_orbit(bi, gs, n, nu, w, true), freeps) };
        if (delta1.size() == 0) continue;  // slot with no symmetries

        vec_t deltap{ onpoints(delta1, cr_perm) };

        size_t k{ position_vec(deltap, sortB(deltap, base)[0]) };  // position of the minimal point of deltap

        // compute permutation omega such that b^omega = delta1[k - 1]
        perm_t omega{ trace_schreier(delta1[k - 1], nu, w) };
        cr_perm = omega * cr_perm;

        // new positions of free indices
        freeps = onpoints(freeps, inverse_perm(omega));

        // note that we do not change base to have i as first member of base.
        gs = stabilizer({ bi }, gs);
    }

    return cr_perm;
}

/*********************************************************************/

/* SGS for a dummyset. */
void SGSofDummyset(perm_t& bD, gs_t& KD, const perm_t& dummies, int sym, size_t n) {
    if (dummies.size() == 0) { bD.resize(0); KD.resize(0); return; }

    // number of pairs of dummies: dp_n
    size_t dp_n{ dummies.size() / 2 };

    perm_t id_Imag = range_vec(n);

    // exchange indices
    KD.resize(dp_n - 1);
    for (size_t i = 0; i < dp_n - 1; ++i) {
        KD[i] = id_Imag;

        // swap elements of consecutive pairs
        KD[i][dummies[2 * i] - 1] = dummies[2 * i + 2];
        KD[i][dummies[2 * i + 1] - 1] = dummies[2 * i + 3];
        KD[i][dummies[2 * i + 2] - 1] = dummies[2 * i];
        KD[i][dummies[2 * i + 3] - 1] = dummies[2 * i + 1];
    }

    // exchange indices of the same pair. If sym != 0 there are dp_n permutations
    if (sym == +1 || sym == -1) {
        KD.resize(2 * dp_n - 1);
        for (size_t i = 0; i < dp_n; ++i) {
            size_t ii{ dp_n - 1 + i };
            KD[ii] = id_Imag;

            // swap elements of pair
            KD[ii][dummies[2 * i] - 1] = dummies[2 * i + 1];
            KD[ii][dummies[2 * i + 1] - 1] = dummies[2 * i];

            if (sym == -1) {  // if mQ == -1, set negative sign
                KD[ii][n - 2] = n;
                KD[ii][n - 1] = n - 1;
            }
        }
    }

    // base of group D
    bD.resize(dp_n);
    for (size_t i = 0; i < dp_n; i++)
        bD[i] = dummies[2 * i];
}

/* SGS for a repeatedset. */
void SGSofRepeatedset(perm_t& bD, gs_t& KD, const perm_t& repes, size_t n) {
    size_t r_n{ repes.size() };
    if (r_n == 0) { bD.resize(0); KD.resize(0); return; }

    perm_t id_Imag = range_vec(n);

    bD.resize(r_n - 1); KD.resize(r_n - 1);
    for (size_t i = 0; i < r_n - 1; i++) {
        bD[i] = repes[i];
        KD[i] = id_Imag;

        // swap elements of pair
        KD[i][repes[i] - 1] = repes[i + 1];
        KD[i][repes[i + 1] - 1] = repes[i];
    }
}

/* Move index in a dummyset.  */
void moveDummyset(size_t firstd, perm_t& dummies) {
    // find position of dummy and relative position of its pair
    size_t pos{ position_vec(dummies, firstd) };
    if (pos != 0) {  // firstd in dummies
        // swap all pairs if firstd found as second
        if (pos % 2 == 0) {  // not 1st member
            pos--;

            // 2nd member: swap all pairs
            for (size_t j = 0; j < dummies.size() / 2; ++j)
                std::swap(dummies[2 * j], dummies[2 * j + 1]);
        }

        // exchange position of pair with first pair
        if (pos != 1) {  // not 1st pair
            // exchange two pairs of dummies
            std::swap(dummies[pos - 1], dummies[0]);
            std::swap(dummies[pos], dummies[1]);
        }
    }
}

/* Move index in a repeated set. */
void moveRepeatedset(size_t firstd, perm_t& repes) {
    // find position of dummy and relative position of its pair
    size_t pos{ position_vec(repes, firstd) };
    if (pos != 0 && pos != 1)  // firstd in repes and not 1st index
        std::swap(repes[pos - 1], repes[0]);
}

/* SGSD for a given list of dummies and repes */
void SGSD(perm_t& bD, gs_t& KD, perm_t& dummies, perm_t& repes,
    size_t firstd, const perm_t& vds, int mQ[], const perm_t& vrs, size_t n) {
    bD.resize(0); KD.resize(0);
    if (dummies.size() == 0 && repes.size() == 0) return;

    perm_t tmpbase; gs_t tmpGS;  // 2020.12

    // loop over all dummysets
    size_t itotal{ 0 };
    for (size_t i = 0; i < vds.size(); ++i) {
        perm_t tmp(dummies.begin() + itotal, dummies.begin() + itotal + vds[i]);
        moveDummyset(firstd, tmp);

        // update dummies
        for (size_t j = itotal; j < vds[i]; ++j)
            dummies[j] = tmp[j - itotal];

        itotal += vds[i];
        SGSofDummyset(tmpbase, tmpGS, tmp, mQ[i], n);

        for (auto b : tmpbase) bD.push_back(b);
        for (auto p : tmpGS)   KD.push_back(p);
    }

    // loop over all repeatedsets
    itotal = 0;
    for (size_t i = 0; i < vrs.size(); ++i) {
        perm_t tmp(repes.begin() + itotal, repes.begin() + itotal + vrs[i]);
        moveRepeatedset(firstd, tmp);

        // update repes
        for (size_t j = itotal; j < vrs[i]; ++j)
            repes[j] = tmp[j - itotal];

        itotal += vrs[i];

        SGSofRepeatedset(tmpbase, tmpGS, tmp, n);
        for (auto b : tmpbase) bD.push_back(b);
        for (auto p : tmpGS)   KD.push_back(p);
    }
}

/*********************************************************************/

/* Remove a first-pair from dummies */
void dropDummyset(size_t firstd, perm_t& vds, perm_t& dummies) {
    size_t itotal{ 0 }, d_n{ dummies.size() };
    if (d_n < 2) return;

    for (size_t i = 0; i < vds.size(); ++i) {
        if (dummies[itotal] == firstd && vds[i] != 0) {
            for (size_t j = itotal; j < d_n - 2; ++j)
                dummies[j] = dummies[j + 2];
            vds[i] -= 2;
            dummies.resize(d_n - 2);
            return;
        }
        itotal += vds[i];
    }
}

/* Remove a first-point from repes */
void dropRepeatedset(size_t firstd, perm_t& vrs, perm_t& repes) {
    size_t itotal{ 0 }, r_n{ repes.size() };
    if (r_n < 1) return;

    for (size_t i = 0; i < vrs.size(); ++i) {
        if (repes[itotal] == firstd && vrs[i] != 0) {
            for (size_t j = itotal; j < r_n - 1; ++j)
                repes[j] = repes[j + 1];
            vrs[i] -= 1;
            repes.resize(r_n - 1);
            return;
        }
        itotal += vrs[i];
    }
}

/*********************************************************************/

/* define ALPHA */
struct alphaStruct {
    vec_t  L;  // We assume that elements of L cannot be repeated.
    perm_t s, d;
    vec_t  o;  // other
};
using alpha_t = std::vector<alphaStruct>;

/* define TAB */
static void TAB(perm_t& s1, perm_t& d1, const alpha_t& ALPHA, const vec_t& L) {
    // search ALPHA for the l corresponding to L
    size_t l{ 0 };
    for (auto k : L)
        l = ALPHA[l].o[k - 1];

    // copy permutations of element l
    s1 = ALPHA[l].s;
    d1 = ALPHA[l].d;
}

/* subroutines F1 */
static void F1(perm_t& list, const vec_t& L, const perm_t& g,
    const alpha_t& ALPHA, const vec_t& Deltab, const vec_t& DeltaD) {
    perm_t s, d;
    TAB(s, d, ALPHA, L);

    // Images of Deltab under sgd
    vec_t tmp{ onpoints(Deltab, (s * g) * d) };

    // orbits of DeltaD containing the points in tmp
    for (size_t c1 = 0; c1 < Deltab.size(); ++c1) {
        size_t oi{ DeltaD[tmp[c1] - 1] };
        if (oi) {
            for (size_t c2 = 1; c2 <= DeltaD.size(); ++c2) {
                if ((DeltaD[c2 - 1] == oi) && (!memberq_vec(list, c2)))
                    list.push_back(c2);
            }
        }
    }
}

// consistency check
static bool consistency(size_t n, size_t lower, size_t upper, const alpha_t& alpha, const perm_t& g) {
    auto sign = [n](const perm_t& perm) { if (n < 2) return +1; return perm[n - 1] == n ? +1 : -1; };

    // detect sign of permutations
    gs_t arrayp, arrayn;
    for (size_t i = lower; i < upper; ++i) {
        perm_t perm{ (alpha[i].s * g) * alpha[i].d };
        (sign(perm) > 0) ? arrayp.push_back(take_vec(perm, n - 2))
            : arrayn.push_back(take_vec(perm, n - 2));  // remove sign
    }

    bool result{ true };
    std::sort(arrayn.begin(), arrayn.end());
    for (const auto& np : arrayp) {
        if (std::binary_search(arrayn.begin(), arrayn.end(), np)) {
            result = false;
            break;
        }
    }

    return result;
}

/* This algorithm is encoded from Renato Portugal et al,
 * with the extensions to repeatedsets.
 *
 * This function gives a canonical representant for the n-permutation g
 * in the double coset S.g.D given by the groups S, described by a SGS
 * (base, GS) and the group D, described by the direct product of
 * the pair-symmetric pairs of dummies and the S_k groups of k
 * repeated indices. Each dummyset has a metric_symmetry sign: if mQ=1
 * the metric is symmetric. If mQ=-1 the metric is antisymmetric
 * (spinor calculus). If mQ=0 there is no metric. */
perm_t double_coset_rep(const perm_t& g, size_t n, const perm_t& base, const gs_t& GS,
    const perm_t& vds_src, const perm_t& dummies_src, int mQ[],
    const perm_t& vrs_src, const perm_t& repes_src) {
    if (n <= 0) return g;

    // copy ... to preserve the const-ness of ...
    perm_t vds(vds_src), dummies(dummies_src), vrs(vrs_src), repes(repes_src);

    //**************************************************************
    //                       DEFINITIONS
    //**************************************************************

    // define ALPHA
    alpha_t ALPHA; vec_t ALPHAstep(n, 0);

    // initialize ALPHA to {} and TAB to {id, id}
    ALPHA.push_back(alphaStruct());
    ALPHA[0].s = ALPHA[0].d = range_vec(n);
    ALPHA[0].o.assign(n, 0);

    ALPHAstep[0] = 0;
    ALPHAstep[1] = 1;

    //*************************************************************
    //               CONSTRUCTION OF BASES
    //*************************************************************

    // all drummies, both the pair-dummies and the repes
    vec_t drummies{ join_vec(dummies, repes) };

    // slots of all those drummies
    vec_t drummyslots{ onpoints(drummies, inverse_perm(g)) };

    // initialize KS, Genset for group S
    gs_t KS{ GS };

    // extend base to bS to cover all positions of drummies.
    vec_t bS{ join_vec(intersection_vec(base, drummyslots),
                      sort_vec(complement_vec(drummyslots, base))) };  // bases for group S

    // generate associated base for sorting names of dummies
    vec_t drummytmp1{ sort_vec(drummies) }, drummytmp2{ sort_vec(bS) };
    vec_t bSsort;
    for (auto k : bS)
        bSsort.push_back(drummytmp1[position_vec(drummytmp2, k) - 1]);

    //*******************
    //**** Main loop ****
    //*******************

    // gs for group D. The number d_n + r_n is an upper bound
    vec_t bD; gs_t KD;
    vec_t L, L1; perm_t s, d, s1, d1;
    gs_t nu, nuD; perm_t w, wD;

    // Note we use i=1..bS.size() instead of the usual i=0 ..(bS.size()-1)
    size_t i; bool result{ true };
    for (i = 1; i <= bS.size(); ++i) {
        // Schreier vector of S
        schreier_vector(nu, w, bS[i - 1], KS, n);
        vec_t Deltab{ orbit(bS[i - 1], KS) };

        // compute SGS for group D. Do not rearrange drummies
        SGSD(bD, KD, dummies, repes, 0, vds, mQ, vrs, n);

        // orbits of D
        vec_t DeltaD{ all_orbits(KD, n) };

        // images of bS[i-1] under elements of S.g.D. Deltab and DeltaD are used by F1
        perm_t IMAGES;
        for (size_t c = ALPHAstep[i - 1]; c < ALPHAstep[i]; ++c)
            F1(IMAGES, ALPHA[c].L, g, ALPHA, Deltab, DeltaD);
        if (IMAGES.size() == 0) continue;  // If there are no images, we have finished

        // find minimum index
        size_t idx{ sortB(IMAGES, bSsort)[0] };

        // recompute SGS of D
        if (dummies.size() > 0 || repes.size() > 0)
            SGSD(bD, KD, dummies, repes, idx, vds, mQ, vrs, n);

        // Schreier vector of D
        schreier_vector(nuD, wD, idx, KD, n);

        // orbit of idx under D
        vec_t Deltap{ orbit(idx, KD) };

        // calculate ALPHA and TAB
        ALPHAstep[i + 1] = ALPHAstep[i];
        for (size_t l = ALPHAstep[i - 1]; l < ALPHAstep[i]; ++l) {
            L = ALPHA[l].L; s = ALPHA[l].s; d = ALPHA[l].d;

            vec_t NEXT{ intersection_vec(onpoints(Deltab, s),
                                        onpoints(Deltap, inverse_perm(g * d))) };
            for (auto next : NEXT) {
                vec_t  L1{ L }; L1.push_back(next);
                perm_t s1{ trace_schreier(onpoint(next, inverse_perm(s)), nu, w) * s };
                perm_t d1{ d * inverse_perm(trace_schreier(onpoint(next, g * d), nuD, wD)) };

                size_t kk{ ALPHAstep[i + 1] };
                ALPHA[l].o[next - 1] = kk;

                ALPHA.push_back(alphaStruct());
                ALPHA[kk].L = L1;
                ALPHA[kk].s = s1;
                ALPHA[kk].d = d1;
                ALPHA[kk].o.assign(n, 0);

                ALPHAstep[i + 1]++;
            }
        }

        { // verify if there are 2 equal permutations of opposite sign in SgD
            result = consistency(n, ALPHAstep[i], ALPHAstep[i + 1], ALPHA, g);
            if (!result) break;
        }

        // find the stabilizers S^(i+1) and D^(i+1)
        KS = stabilizer({ bS[i - 1] }, KS);
        dropDummyset(idx, vds, dummies);
        dropRepeatedset(idx, vrs, repes);
    }

    perm_t cr_perm;
    if (result == false)
        cr_perm = perm_t(n, 0);
    else {
        size_t l{ ALPHAstep[i - 1] };
        cr_perm = (ALPHA[l].s * g) * ALPHA[l].d;
    }
    return cr_perm;
}

/*********************************************************************/

/* This function finds a canonical representant of the permutation PERM
 * in the double_coset with group S (slot symmetries) and group D
 * (dummy index or repeated index symmetries).
 *
 * There are two steps: first S, then S and D. The "slot" group S is
 * given through the generating set SGS (with m n-permutations).
 * The algorithm first calls right_coset_rep with PERM and the free indices
 * converting PERM into PERM1. The SGS is then stabilized with respect
 * to those points. Then the double_coset_rep algorithm is called with
 * PERM1.
 *
 * PERM:    permutation (Imag notation) to canonicalize
 * n:       degree of perm
 * base:    sorted list of points for the SGS
 * GS:      the list of permutations forming the GS
 * freeps:  list of initial names of free indices
 * vds:     list of lengths of dummysets
 * dummies: list with pairs of names dummies
 * mQ:      list (with length of vds) with symmetry signs
 * vrs:     list of lengths of repeatedsets
 * repes:   list with repeated indices */
perm_t canonical_perm_ext(const perm_t& PERM, size_t n, const perm_t& base, const gs_t& GS,
    const perm_t& frees, const perm_t& vds, const perm_t& dummies, int* mQ,
    const perm_t& vrs, const perm_t& repes) {
    if (n <= 0) return PERM;

    // compute slots of free indices
    vec_t freeps{ onpoints(frees, inverse_perm(PERM)) };

    perm_t PERM1{ right_coset_rep(PERM, n, base, GS, freeps) };
    if (dummies.size() + repes.size() == 0)  // no drummy indices
        return PERM1;
    else
        return double_coset_rep(PERM1, n,
            complement_vec(base, freeps), stabilizer(freeps, GS),
            vds, dummies, mQ, vrs, repes);
}

/*********************************************************************/
/************************* make_perm_group ***************************/
/*********************************************************************/

gs_t NULL_GS;

// Dimino's Algorithm (Butler, 1991)
static void make_perm_group_priv(gs_t& gr, const gs_t& GS, size_t n) {
    auto isid_perm = [](const perm_t& v) { return v == range_vec(v.size()); };

    gr.resize(0);
    gr.push_back(range_vec(n));

    size_t m = GS.size();
    if (m * n <= 0) return;

    // treat the special case <s1>
    perm_t g(GS[0]);  // g = s1
    while (!isid_perm(g)) {
        gr.push_back(g);
        g *= GS[0];   // g = g * s1
    }

    // treat remaining inductive levels
    size_t prev_order, rep_pos;
    for (size_t i = 2; i <= m; ++i) {
        g = GS[i - 1];  // g = si
        if (!memberq_gs(gr, g)) {
            prev_order = gr.size();  // size of H_{i-1}

            gr.push_back(g);
            for (size_t j = 2; j <= prev_order; ++j)
                gr.push_back(gr[j - 1] * g);

            rep_pos = prev_order + 1;   // position of coset representative
            while (true) {
                for (size_t k = 1; k <= i; ++k) {  // for each s in Si
                    g = gr[rep_pos - 1] * GS[k - 1];
                    if (!memberq_gs(gr, g)) {
                        gr.push_back(g);
                        for (size_t j = 2; j <= prev_order; ++j)
                            gr.push_back(gr[j - 1] * g);
                    }
                }
                rep_pos += prev_order;  // position of next coset representative
                if (rep_pos > gr.size()) break;
            }
        }
    }
}

void make_perm_group(gs_t& group, const gs_t& GS, size_t n) {
    if (n <= 0) { group = NULL_GS; return; }
    make_perm_group_priv(group, GS, n);
}
