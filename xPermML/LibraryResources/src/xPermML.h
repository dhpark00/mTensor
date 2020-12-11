
#ifndef _XPERM_ML_CPP_
#define _XPERM_ML_CPP_

#include <vector>
#include <algorithm>
#include <iterator>   // std::back_inserter
#include <string>

/*********************************************************************/
using vec_t  = std::vector<size_t>;  // generic unsigned vector
using perm_t = std::vector<size_t>;  // permutation in Imag notation
using gs_t   = std::vector<perm_t>;

extern perm_t NULL_Imag;

/*********************************************************************/
/********************** canonical_perm_ext ***************************/
/*********************************************************************/

// true if 'k' in vec
inline bool memberq_vec(const vec_t& vec, size_t k) {
    return std::find(vec.begin(), vec.end(), k) != vec.end();
}

extern vec_t  complement_vec(const vec_t& v1, const vec_t& v2);
extern vec_t  intersection_vec(const vec_t& v1, const vec_t& v2);
extern vec_t  join_vec(vec_t v1, vec_t v2);
extern size_t position_vec(const vec_t& vec, size_t k);
extern vec_t  range_vec(size_t n);
extern vec_t  sort_vec(vec_t vec);
extern vec_t  take_vec(const vec_t& vec, size_t k);

/*********************************************************************/

extern void         operator *=(perm_t& lhs, const perm_t& rhs);
extern const perm_t operator *(perm_t v1, const perm_t& v2);

/*********************************************************************/

extern perm_t inverse_perm(const perm_t& vec);
extern size_t onpoint(size_t point, const perm_t& perm);
extern vec_t  onpoints(const perm_t& lst, const perm_t& perm);
extern perm_t sortB(const perm_t& lst, const vec_t& B);

/*********************************************************************/

extern perm_t orbit(size_t point, const gs_t& GS);
extern perm_t all_orbits(const gs_t& GS, size_t n);
extern perm_t schreier_orbit(size_t point, const gs_t& GS, size_t n, gs_t& nu, perm_t& w, bool init);
extern void   schreier_vector(gs_t& nu, perm_t& w, size_t point, const gs_t& GS, size_t n);
extern perm_t trace_schreier(size_t point, const gs_t& nu, const perm_t& w);

/*********************************************************************/

extern gs_t   stabilizer(const perm_t& points, const gs_t& GS);
extern perm_t right_coset_rep(const perm_t& p, size_t n, const perm_t& base, const gs_t& GS, perm_t& freeps);

/*********************************************************************/

extern void SGSofDummyset(perm_t& bD, gs_t& KD, const perm_t& dummies, int sym, size_t n);
extern void SGSofRepeatedset(perm_t& bD, gs_t& KD, const perm_t& repes, size_t n);
extern void moveDummyset(size_t firstd, perm_t& dummies);
extern void moveRepeatedset(size_t firstd, perm_t& repes);
extern void SGSD(perm_t& bD, gs_t& KD, perm_t& dummies, perm_t& repes,
                 size_t firstd, const perm_t& vds, int mQ[], const perm_t& vrs, size_t n);

/*********************************************************************/

extern void dropDummyset(size_t firstd, perm_t& vds, perm_t& dummies);
extern void dropRepeatedset(size_t firstd, perm_t& vrs, perm_t& repes);

extern perm_t double_coset_rep(const perm_t& g, size_t n, const perm_t& base, const gs_t& GS,
                               const perm_t& vds_src, const perm_t& dummies_src, int mQ[],
                               const perm_t& vrs_src, const perm_t& repes_src);

/*********************************************************************/

extern perm_t canonical_perm_ext(const perm_t& PERM, size_t n, const perm_t& base, const gs_t& GS,
                                 const perm_t& frees, const perm_t& vds, const perm_t& dummies, int *mQ,
                                 const perm_t& vrs, const perm_t& repes);

/*********************************************************************/
/************************* make_perm_group ***************************/
/*********************************************************************/

// true if 'perm' in gs. (cf: position_list in xperm)
inline bool memberq_gs(const gs_t& GS, const perm_t& perm) {
    return std::find(GS.begin(), GS.end(), perm) != GS.end();
}

extern gs_t NULL_GS;

extern void make_perm_group(gs_t& group, const gs_t& GS, size_t n);

/*********************************************************************/

#endif
