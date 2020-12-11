/* 2020.12.10 by dhpark */
/**********************************************************************
 * xPermML.tm to link the xPermML.cpp code                            *
 **********************************************************************/

#include "mathlink.h"
#include <cstdlib>

/**********************************************************************
 *                            PACKAGE                                 *
 **********************************************************************/

/* std::max, std::min with windows max, min */
#ifdef max

#undef max
#undef min

#endif

#include "xPermML.cpp"

static void gs2arr(int *arr, const gs_t& GS, size_t n) {
    for (size_t i = 0; i < GS.size(); ++i)
        for (size_t j = 0; j < n; ++j)
            arr[i*n + j] = GS[i][j];
}

static void arr2gs(gs_t& GS, int *arr, size_t n) {
    for (size_t i = 0; i < GS.size(); ++i)
        for (size_t j = 0; j < n; ++j)
            GS[i][j] = arr[i*n + j];
}

/**********************************************************************
 *                           INTERFACE                                *
 **********************************************************************/

/**********************************************************************/
:Begin:
:Function:      ML_canonical_perm
:Pattern:       mTensor`xPermML`Private`MLCanonicalPerm[ mTensor`xPermML`Private`perm_List,
                                                         mTensor`xPermML`Private`n_Integer,
                                                         mTensor`xPermML`Private`base_List,
                                                         mTensor`xPermML`Private`GS_List,
                                                         mTensor`xPermML`Private`freeps_List,
                                                         mTensor`xPermML`Private`vds_List,
                                                         mTensor`xPermML`Private`dummies_List,
                                                         mTensor`xPermML`Private`mQ_List,
                                                         mTensor`xPermML`Private`vrs_List,
                                                         mTensor`xPermML`Private`repes_List ]
:Arguments:     { mTensor`xPermML`Private`perm,
                  mTensor`xPermML`Private`n,
                  mTensor`xPermML`Private`base,
                  mTensor`xPermML`Private`GS,
                  mTensor`xPermML`Private`freeps,
                  mTensor`xPermML`Private`vds,
                  mTensor`xPermML`Private`dummies,
                  mTensor`xPermML`Private`mQ,
                  mTensor`xPermML`Private`vrs,
                  mTensor`xPermML`Private`repes }
:ArgumentTypes: { IntegerList,
                  Integer,
                  IntegerList,
                  IntegerList,
                  IntegerList,
                  IntegerList,
                  IntegerList,
                  IntegerList,
                  IntegerList,
                  IntegerList }
:ReturnType:    Manual
:End:

:Evaluate:

void ML_canonical_perm(int *arrPERM,    long p_n,
                       int n,
                       int *arrBase,    long b_n,
                       int *arrGS,      long mn,
                       int *arrFreeps,  long f_n,
                       int *arrVds,     long vds_n,
                       int *arrDummies, long d_n,
                       int *mQ,         long mQ_n,
                       int *arrVrs,     long vrs_n,
                       int *arrRepes,   long r_n)
{
    perm_t PERM(arrPERM, arrPERM + p_n);
    vec_t  base(arrBase, arrBase + b_n);
    gs_t   GS(mn/n, vec_t(n)); arr2gs(GS, arrGS, n);
    vec_t  freeps(arrFreeps, arrFreeps + f_n);
    vec_t  vds(arrVds, arrVds + vds_n);
    vec_t  dummies(arrDummies, arrDummies + d_n);
    vec_t  vrs(arrVrs, arrVrs + vrs_n);
    vec_t  repes(arrRepes, arrRepes + r_n);
    perm_t cr_perm{canonical_perm_ext(PERM, n, base, GS,
                                      freeps, vds, dummies, mQ, vrs, repes)};

    int *cperm = (int *) malloc(n*sizeof(int));

        for (size_t i = 0; i < cr_perm.size(); ++i)
            cperm[i] = cr_perm[i];

        int error = MLError(stdlink);
        if (error) {
            MLPutFunction(stdlink, "Print", 1);
            MLPutString(stdlink, MLErrorMessage(stdlink));
        }
        else
            MLPutIntegerList(stdlink, cperm, n);

    free(cperm);
    return;
}

/**********************************************************************/
:Begin:
:Function:      ML_MakePermGroup
:Pattern:       mTensor`xPermML`Private`MLMakePermGroup[ mTensor`xPermML`Private`arr_List,
                                                         mTensor`xPermML`Private`n_Integer ]
:Arguments:     {mTensor`xPermML`Private`arr, mTensor`xPermML`Private`n}
:ArgumentTypes: {IntegerList, Integer}
:ReturnType:    Manual
:End:

:Evaluate:

void ML_MakePermGroup(int *arrGS, long mn, int n) {
    gs_t GS(mn/n, vec_t(n)); arr2gs(GS, arrGS, n);

    gs_t group;
    make_perm_group(group, GS, n);
    size_t order = group.size();

    int *gr = (int *) malloc(order*n*sizeof(int));

        gs2arr(gr, group, n);
        MLPutIntegerList(stdlink, gr, order*n);

    free(gr);

    return;
}

/**********************************************************************/

/**********************************************************************
 *                            COMPATIBILITY                           *
 **********************************************************************/

#if MACINTOSH_MATHLINK

int main( int argc, char* argv[])
{
    /* Due to a bug in some standard C libraries that have shipped with
     * MPW, zero is passed to MLMain below.  (If you build this program
     * as an MPW tool, you can change the zero to argc.)
     */
    argc = argc; /* suppress warning */
    return MLMain( 0, argv);
}

#elif WINDOWS_MATHLINK

int PASCAL WinMain( HINSTANCE hinstCurrent, HINSTANCE hinstPrevious, LPSTR lpszCmdLine, int nCmdShow)
{
    char  buff[512];
    char FAR * buff_start = buff;
    char FAR * argv[32];
    char FAR * FAR * argv_end = argv + 32;

    hinstPrevious = hinstPrevious; /* suppress warning */

    if( !MLInitializeIcon( hinstCurrent, nCmdShow)) return 1;
    MLScanString( argv, &argv_end, &lpszCmdLine, &buff_start);
    return MLMain( argv_end - argv, argv);
}

#else

int main(int argc, char* argv[])
{
    return MLMain(argc, argv);
}

#endif
