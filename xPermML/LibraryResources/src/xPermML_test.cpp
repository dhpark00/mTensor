
#include "xPermML.h"
#include <iostream>

/*********************************************************************/
#include <cassert>

using std::cout;

std::ostream& operator <<(std::ostream& os, const perm_t& v) {
    os << "(";
    if (v.size() > 0) {
        os << v[0];
         for (size_t i = 1; i < v.size(); ++i)
            os << "," << v[i];
    }
    os << ")";

    return os;
}

std::ostream& operator <<(std::ostream& os, const gs_t& gs) {
    os << "{";
    for (auto v : gs)
        os << " " << v;
    os << " }";
    return os;
}

/***** mode 1 *****/

void test_complement_vec() {
    cout << "complement_vec:\n";

    vec_t v1{2,3}, v2{1,5,2}, v3, v;

    v = complement_vec(v1, v2);
    cout << "    " << v1 << " - " << v2 << " -> " << v << '\n';
    assert(v == vec_t({3}));

    v = complement_vec(v2, v1);
    cout << "    " << v2 << " - " << v1 << " -> " << v << '\n';
    assert(v == vec_t({1,5}));

    v = complement_vec(v3, v2);
    cout << "    " << v3 << " - " << v2 << " -> " << v << '\n';
    assert(v == NULL_Imag);
}

void test_memberq_vec() {
    cout << "memberq_vec:\n";

    vec_t v1, v2{1,2,3,4,5}, v3{2,1,5,4,2};
    size_t k = 2;

    cout << "    " << v1 << ", " << k << " -> " << std::boolalpha << memberq_vec(v1, k) << '\n';
    assert(memberq_vec(v1, k) == false);

    cout << "    " << v2 << ", " << k << " -> " << std::boolalpha << memberq_vec(v2, k) << '\n';
    assert(memberq_vec(v2, k) == true);

    cout << "    " << v3 << ", " << k << " -> " << std::boolalpha << memberq_vec(v3, k) << '\n';
    assert(memberq_vec(v3, k) == true);
}

void test_intersection_vec() {
    cout << "intersection_vec:\n";

    vec_t v1, v2{6,1,8,3,2,9,5,4}, v3{1,2,3,4,5}, v;

    v = intersection_vec(v1, v2);
    cout << "    " << v1 << ", " << v2 << " -> " << v << '\n';
    assert(v == v1);

    v = intersection_vec(v2, v3);
    cout << "    " << v2 << ", " << v3 << " -> " << v << '\n';
    assert(v == vec_t({1,3,2,5,4}));
}

void test_join_vec() {
    cout << "join_vec:\n";

    vec_t v1{3,1}, v2{1,2,5}, v3, v;

    v = join_vec(v1, v2);
    cout << "    " << v1 << " + " << v2 << " -> " << v << '\n';
    assert(v == vec_t({3,1,1,2,5}));

    v = join_vec(v1, v3);
    cout << "    " << v1 << " + " << v3 << " -> " << v << '\n';
    assert(v == v1);

    v = join_vec(v3, v2);
    cout << "    " << v3 << " + " << v2 << " -> " << v << '\n';
    assert(v == v2);

    // rvalue reference
    v = join_vec(vec_t({3,1}), vec_t({1,2,5}));
    cout << "    " << v1 << " + " << v2 << " -> " << v << '\n';
    assert(v == vec_t({3,1,1,2,5}));

    v = join_vec(vec_t({3,1}), vec_t({}));
    cout << "    " << v1 << " + " << v3 << " -> " << v << '\n';
    assert(v == v1);

    v = join_vec(vec_t({}), vec_t({1,2,5}));
    cout << "    " << v3 << " + " << v2 << " -> " << v << '\n';
    assert(v == v2);
}

void test_position_vec() {
    cout << "position_vec:\n";

    vec_t v1, v2{1,2,3,4,5}, v3{2,1,5,4,3}, v4{2,1,5,4,2};
    size_t k = 2;

    cout << "    " << v1 << ", " << k << " -> " << position_vec(v1, k) << '\n';
    assert(position_vec(v1, k) == 0);

    cout << "    " << v2 << ", " << k << " -> " << position_vec(v2, k) << '\n';
    assert(position_vec(v2, k) == 2);

    cout << "    " << v3 << ", " << k << " -> " << position_vec(v3, k) << '\n';
    assert(position_vec(v3, k) == 1);

    cout << "    " << v4 << ", " << k << " -> " << position_vec(v4, k) << '\n';
    assert(position_vec(v4, k) == 5);
}

void test_range_vec() {
    cout << "range_vec:\n";

    vec_t v = range_vec(0);
    cout << "    0 -> " << v << '\n';
    assert(v == NULL_Imag);

    v = range_vec(1);
    cout << "    1 -> " << v << '\n';
    assert(v == vec_t({1}));

    v = range_vec(5);
    cout << "    5 -> " << v << '\n';
    assert(v == vec_t({1,2,3,4,5}));
}

void test_sort_vec() {
    cout << "sort:\n";

    vec_t v1, v2{2,1,5,4,3}, v;

    v = sort_vec(v1);
    cout << "    " << v1 << " -> " << v << '\n';
    assert(v == v1);

    v = sort_vec(v2);
    cout << "    " << v2 << " -> " << v << '\n';
    assert(v == vec_t({1,2,3,4,5}));

    // rvalue reference
    v = sort_vec(vec_t({}));
    cout << "    " << v1 << " -> " << v << '\n';
    assert(v == v1);

    v = sort_vec(vec_t({2,1,5,4,3}));
    cout << "    " << v2 << " -> " << v << '\n';
    assert(v == vec_t({1,2,3,4,5}));
}

void test_take_vec() {
    cout << "take_vec:\n";

    vec_t v1{1,2,3,4,5}, v;

    v = take_vec(v, 2);
    cout << "    " << v << ", 2 -> " << v << '\n';
    assert(v == NULL_Imag);

    v = take_vec(v1, 0);
    cout << "    " << v1 << ", 0 -> " << v << '\n';
    assert(v == NULL_Imag);

    v = take_vec(v1, 1);
    cout << "    " << v1 << ", 1 -> " << v << '\n';
    assert(v == vec_t({1}));

    v = take_vec(v1, 2);
    cout << "    " << v1 << ", 2 -> " << v << '\n';
    assert(v == vec_t({1,2}));

    v = take_vec(v1, 4);
    cout << "    " << v1 << ", 4 -> " << v << '\n';
    assert(v == vec_t({1,2,3,4}));

    v = take_vec(v1, 6);
    cout << "    " << v1 << ", 6 -> " << v << '\n';
    assert(v == v1);
}

/***** mode 2 *****/

void test_product_perm() {
    cout << "product_perm:\n";

    perm_t perm1, perm2{3,2,1}, perm3{3,1,2}, perm;

    perm = perm1 * perm;
    cout << "    " << perm1 << " * " << perm2 << " -> " << perm << '\n';
    assert(perm == perm1);  // {} * perm -> {}

    perm = perm2 * perm3;
    cout << "    " << perm2 << " * " << perm3 << " -> " << perm << '\n';
    assert(perm == perm_t({2,1,3}));

    cout << "    " << perm << " *= " << perm2;
    perm *= perm2;
    cout << " -> " << perm << '\n';
    assert(perm == perm_t({2,3,1}));

    // rvalue reference
    perm = perm_t({3,2,1}) * perm_t({3,1,2});
    cout << "    " << perm2 << " * " << perm3 << " -> " << perm << '\n';
    assert(perm == perm_t({2,1,3}));
}

void test_inverse_perm() {
    cout << "inverse_perm:\n";

    perm_t perm1, perm2{2,1,4,5,3}, perm;

    perm = inverse_perm(perm1);
    cout << "    " << perm1 << " -> " << perm << '\n';
    assert(perm == perm1);

    perm = inverse_perm(perm2);
    cout << "    " << perm2 << " -> " << perm << '\n';
    assert(perm == perm_t({2,1,5,3,4}));
}

void test_onpoint() {
    cout << "onpoint and onpoints:\n";

    perm_t perm1, perm2{2,1,3,4,5};
    size_t point = 1;

    cout << "    onpoint: " << point << ", " << perm1 << " -> " << onpoint(point, perm1) << '\n';
    assert(onpoint(point, perm1) == point);

    cout << "    onpoint: " << point << ", " << perm2 << " -> " << onpoint(point, perm2) << "\n\n";
    assert(onpoint(point, perm2) == 2);

    vec_t pts{1,2,3,4,5};
    cout << "    onpoints: " << pts << ", " << perm2 << " -> " << onpoints(pts, perm2) << "\n";
    assert(onpoints(pts, perm2) == perm2);
}

void test_sortB() {
    cout << "sortB:\n";

    perm_t v1, v2{2,1,5,4,3}, dest;
    vec_t base{2, 3};

    dest = sortB(v1, base);
    cout << "    " << v1 << ", " << base << " -> " << dest << '\n';
    assert(dest == v1);

    dest = sortB(v2, base);
    cout << "    " << v2 << ", " << base << " -> " << dest << '\n';
    assert(dest == perm_t({2,3,1,4,5}));
}

/***** mode 3 *****/

void test_orbit() {
    gs_t GS1, GS2({{2,3,4,1}});
    perm_t perm1{1}, perm2{1,2,3,4};
    perm_t orb;
    size_t point = 1;

    cout << "orbit:" << '\n';

    orb = orbit(point, GS1);
    cout << "    " << point << ", " << GS1 << " -> " << orb << '\n';
    assert(perm1 == orb);

    orb = orbit(point, GS2);
    cout << "    " << point << ", " << GS2 << " -> " << orb << "\n\n";
    assert(perm2 == orb);

    cout << "all_orbits:" << '\n';

    perm_t perm3, perm4{1, 1, 1, 1}, perm5{1, 1, 2, 3, 3}, orbits;
    gs_t GS3({{ 2,1,3,4,5 }, { 1,2,3,5,4 }});
    size_t n1 = 0, n2 = GS2[0].size(), n3 = GS3[0].size();

    orbits = all_orbits(GS1, n1);
    cout << "    " << GS1 << ", " << n1 << " -> " << orbits << '\n';
    assert(perm3 == orbits);

    orbits = all_orbits(GS2, n2);
    cout << "    " << GS2 << ", " << n2 << " -> " << orbits << '\n';
    assert(perm4 == orbits);

    orbits = all_orbits(GS3, n3);
    cout << "    " << GS3 << ", " << n3 << " -> " << orbits << '\n';
    assert(perm5 == orbits);
}

void test_schreier_orbit() {
    perm_t perm1{1}, perm2{1,4,3,2}, perm3{5,4}, perm4{6};
    gs_t GS1, GS2({{4,1,2,3}}), GS3({{2,1,3,4,5}, {1,2,3,5,4}});
    perm_t orb;
    gs_t nu; perm_t w;

    cout << "schreier_orbit:" << '\n';

    orb = schreier_orbit(1, GS1, 0, nu, w, true);
    cout << "    1, " << GS1 << " -> " << orb << '\n';
    cout << "        nu: " << nu << '\n';
    cout << "        w:  " << w << '\n';
    assert(perm1 == orb);

    orb = schreier_orbit(1, GS2, 4, nu, w, true);
    cout << "    1, " << GS2 << " -> " << orb << '\n';
    cout << "        nu: " << nu << '\n';
    cout << "        w:  " << w << '\n';
    assert(perm2 == orb);

    orb = schreier_orbit(5, GS3, 5, nu, w, true);
    cout << "    5, " << GS3 << " -> " << orb << '\n';
    cout << "        nu: " << nu << '\n';
    cout << "        w:  " << w << '\n';
    assert(perm3 == orb);

    orb = schreier_orbit(6, GS3, 5, nu, w, true);
    cout << "    6, " << GS3 << " -> " << orb << '\n';
    cout << "        nu: " << nu << '\n';
    cout << "        w:  " << w << '\n';
    assert(perm4 == orb);
}

void test_schreier_vector() {
    cout << "schreier_vector:" << '\n';

    gs_t GS1, GS2({{4, 1, 2, 3}}), GS3({{2,1,3,4,5}, {1,2,3,5,4}});
    perm_t perm1, perm2{2,0,4,1}, perm3{0,1,0,0,4};
    gs_t nu; perm_t w;

    schreier_vector(nu, w, 5, GS1, 0);
    cout << "    5, " << GS1 << " ->" << '\n';
    cout << "            ()" << '\n';
    cout << "        nu: " << nu << '\n';
    cout << "        w:  " << w << "\n\n";
    assert(perm1 == w);

    schreier_vector(nu, w, 2, GS2, 4);
    cout << "    2, " << GS2 << " ->" << '\n';
    cout << "            (1 2 3 4)" << '\n';
    cout << "        nu: " << nu << '\n';
    cout << "        w:  " << w << "\n\n";
    assert(perm2 == w);

    schreier_vector(nu, w, 4, GS3, 5);
    cout << "    4, " << GS3 << " ->" << '\n';
    cout << "            (1 2 3 4 5)" << '\n';
    cout << "        nu: " << nu << '\n';
    cout << "        w:  " << w << "\n\n";
    assert(perm3 == w);

    schreier_vector(nu, w, 6, GS3, 5);
    cout << "    6, " << GS3 << " ->" << '\n';
    cout << "            (1 2 3 4 5)" << '\n';
    cout << "        nu: " << nu << '\n';
    cout << "        w:  " << w << '\n';
    assert(perm3 == w);
}

void test_trace_schreier() {
    gs_t nu1; perm_t w1, perm1;
    gs_t GS({{2,1,3,4,5}, {1,2,3,5,4}}), nu2; perm_t w2, perm2;
    perm_t perm3{1,2,3,4,5}, perm4{2,1,3,4,5}, perm5{1,2,3,5,4};

    cout << "trace_schreier:" << '\n';

    perm1 = trace_schreier(2, nu1, w1);
    cout << "    2, nu:" << nu1 << ", w:" << w1
         << " -> " << perm1 << '\n';
    assert(perm1 == w1);

    schreier_vector(nu2, w2, 1, GS, 5);
    cout << "\n    schreier_vector:\n";
    cout << "    1, GS:" << GS << " ->" << '\n';
    cout << "            (1 2 3 4 5)" << '\n';
    cout << "        nu: " << nu2 << '\n';
    cout << "        w:  " << w2 << "\n\n";

    perm2 = trace_schreier(6, nu2, w2);
    cout << "    6 <-- " << perm2 << '\n';

    perm2 = trace_schreier(1, nu2, w2);
    cout << "    1 <--" << perm2 << "-- " << w2[1 - 1] << '\n';
    assert(perm2 == perm3);

    perm2 = trace_schreier(2, nu2, w2);
    cout << "    2 <--" << perm2 << "-- " << w2[2 - 1] << '\n';
    assert(perm2 == perm4);

    perm2 = trace_schreier(3, nu2, w2);
    cout << "    3 <--" << perm2 << "-- " << w2[3 - 1] << '\n';
    assert(perm2 == perm3);

    perm2 = trace_schreier(4, nu2, w2);
    cout << "    4 <--" << perm2 << "-- " << w2[4 - 1] << '\n';
    assert(perm2 == perm3);

    perm2 = trace_schreier(5, nu2, w2);
    cout << "    5 <--" << perm2 << "-- " << w2[5 - 1] << '\n';
    assert(perm2 == perm5);
}

/***** mode 4 *****/

void test_stabilizer() {
    cout << "stabilizer:" << '\n';

    perm_t pts{1,2};
    gs_t GS1, GS2({{3,2,1,4,6,7,5},{1,2,4,3,6,5,7}}), subGS;

    subGS = stabilizer(take_vec(pts, 0), GS1);
    cout << "    " << take_vec(pts, 0) << ", " << GS1
        << " -> " << subGS << '\n';
    assert(subGS.empty() == true);

    subGS = stabilizer(take_vec(pts, 1), GS2);
    cout << "    " << take_vec(pts, 1) << ", " << GS2
        << " -> " << subGS << '\n';
    assert(subGS[0] == GS2[1]);

    subGS = stabilizer(pts, GS2);
    cout << "    " << pts << ", " << GS2
        << " -> " << subGS << '\n';
    assert(subGS[0] == GS2[1]);
}

void test_right_coset_rep() {
    cout << "right_coset_rep:" << '\n';

    perm_t perm1, cr_perm1, base1{1,3};
    gs_t GS1;
    perm_t freeps1;
    size_t n1 = 0;

    cout << "    " << perm1 << ", <" << base1 << ", " << GS1 << "> -> ";
    cr_perm1 = right_coset_rep(perm1, n1, base1, GS1, freeps1);
    cout << cr_perm1 << '\n';
    assert(cr_perm1 == perm1);

    perm_t perm2{2,1,4,3}, perm2rc{1,2,3,4}, cr_perm2, base2{1,2,3};
    gs_t GS2({{3,4,2,1}, {4,3,2,1}});
    perm_t freeps2{1,2,3};
    size_t n2 = 4;

    cout << "    " << perm2 << ", <" << base2 << ", " << GS2 << "> -> ";
    cr_perm2 = right_coset_rep(perm2, n2, base2, GS2, freeps2);
    cout << cr_perm2 << '\n';
    assert(cr_perm2 == perm2rc);

    perm_t perm3{2,3,1,4}, perm3rc{1,4,2,3}, cr_perm3, base3{1,2,3};
    gs_t GS3({{2,1,3,4}, {3,4,1,2}, {1,2,4,3}});
    perm_t freeps3{1,2,3,4};
    size_t n3 = 4;

    cout << "    " << perm3 << ", <" << base3 << ", " << GS3 << "> -> ";
    cr_perm3 = right_coset_rep(perm3, n3, base3, GS3, freeps3);
    cout << cr_perm3 << '\n';
    assert(cr_perm3 == perm3rc);

    perm_t perm4{2,3,1,4,5,6}, perm4rc{1,4,2,3,5,6}, cr_perm4, base4{1,2,3};
    gs_t GS4({{2,1,3,4,6,5}, {3,4,1,2,5,6}, {1,2,4,3,6,5}});
    perm_t freeps4{1,2,3,4,5,6};
    size_t n4 = 6;

    cout << "    " << perm4 << ", <" << base4 << ", " << GS4 << ">" << '\n' << "        -> ";
    cr_perm4 = right_coset_rep(perm4, n4, base4, GS4, freeps4);
    cout << cr_perm4 << '\n';
    assert(cr_perm4 == perm4rc);

    perm_t perm5{6,5,4,3,2,1,7,8}, perm5rc{6,5,1,3,2,4,8,7}, cr_perm5, base5{1,2,3,4,5,6};
    gs_t GS5({{1,2,5,4,3,6,8,7}, {1,2,3,4,6,5,8,7}});
    perm_t freeps5{1,2,3,4,5,6};
    size_t n5 = 8;

    cout << "    " << perm5 << ", <" << base5 << ", " << GS5 << ">" << '\n' << "        -> ";
    cr_perm5 = right_coset_rep(perm5, n5, base5, GS5, freeps5);
    cout << cr_perm5 << '\n';
    assert(cr_perm5 == perm5rc);

    perm_t perm6{2,1,4,3,5,6}, perm6rc{1,2,3,4,5,6}, cr_perm6, base6{1,2,3,4};
    gs_t GS6({{4,3,2,1,5,6}, {3,4,2,1,6,5}, {1,2,4,3,6,5}});
    perm_t freeps6{1,2,3,4};
    size_t n6 = 6;

    cout << "    " << perm6 << ", <" << base6 << ", " << GS6 << ">" << '\n' << "        -> ";
    cr_perm6 = right_coset_rep(perm6, n6, base6, GS6, freeps6);
    cout << cr_perm6 << '\n';
    assert(cr_perm6 == perm6rc);

    perm_t perm7{4,1,3,2}, perm7rc{1,4,3,2}, cr_perm7, base7{1, 3};
    gs_t GS7({{2,1,3,4}, {3,4,1,2}, {1,2,4,3}});
    perm_t freeps7{1,2,3,4};
    size_t n7 = 4;

    cout << "    " << perm7 << ", <" << base7 << ", " << GS7 << ">" << '\n' << "        -> ";
    cr_perm7 = right_coset_rep(perm7, n7, base7, GS7, freeps7);
    cout << cr_perm7 << '\n';
    assert(cr_perm7 == perm7rc);
}

/***** mode 5 *****/

void test_SGSofDummyset() {
    cout << "SGSofDummyset:" << '\n';

    perm_t bD1, bD1rc{1,3};
    gs_t KD1, KD1rc({{3,4,1,2}});
    perm_t dummies1{1,2,3,4};
    int sym1 = 0;
    size_t n1 = 4;

    cout << "    " << dummies1 << ", " << sym1;
    SGSofDummyset(bD1, KD1, dummies1, sym1, n1);
    cout << " -> <" << bD1 << ", " << KD1 << ">" << '\n';
    assert(bD1 == bD1rc);
    assert(KD1 == KD1rc);

    perm_t bD2, bD2rc{1,3};
    gs_t KD2, KD2rc({{3,4,1,2}, {2,1,3,4}, {1,2,4,3}});
    perm_t dummies2{1,2,3,4};
    int sym2 = +1;
    size_t n2 = 4;

    cout << "    " << dummies2 << ", " << sym2;
    SGSofDummyset(bD2, KD2, dummies2, sym2, n2);
    cout << " -> <" << bD2 << ", " << KD2 << ">" << '\n';
    assert(bD2 == bD2rc);
    assert(KD2 == KD2rc);

    perm_t bD3, bD3rc{1,3};
    gs_t KD3, KD3rc({{3,4,1,2,5,6}, {2,1,3,4,6,5}, {1,2,4,3,6,5}});
    perm_t dummies3{1,2,3,4};
    int sym3 = -1;
    size_t n3 = 6;

    cout << "    " << dummies3 << ", " << sym3;
    SGSofDummyset(bD3, KD3, dummies3, sym3, n3);
    cout << " -> <" << bD3 << ", " << KD3 << ">" << '\n';
    assert(bD3 == bD3rc);
    assert(KD3 == KD3rc);

    perm_t bD4, bD4rc{1,3,5};
    gs_t KD4, KD4rc({{3,4,1,2,5,6}, {1,2,5,6,3,4}, {2,1,3,4,5,6}, {1,2,4,3,5,6}, {1,2,3,4,6,5}});
    perm_t dummies4{1,2,3,4,5,6};
    int sym4 = +1;
    size_t n4 = 6;

    cout << "    " << dummies4 << ", " << sym4;
    SGSofDummyset(bD4, KD4, dummies4, sym4, n4);
    cout << " -> <" << bD4 << ", " << KD4 << ">" << '\n';
    assert(bD4 == bD4rc);
    assert(KD4 == KD4rc);
}

void test_SGSofRepeatedset() {
    cout << "SGSofRepeatedset:" << '\n';

    perm_t bD1, bD1rc{1,3};
    gs_t KD1, KD1rc({{3,2,1,4,5}, {1,2,5,4,3}});
    perm_t repes1{1,3,5};
    size_t n1 = 5;

    cout << "    " << repes1 << " -> <";
    SGSofRepeatedset(bD1, KD1, repes1, n1);
    cout << bD1 << ", " << KD1 << ">" << '\n';
    assert(bD1 == bD1rc);
    assert(KD1 == KD1rc);
}

void test_moveDummyset() {
    cout << "moveDummyset:" << '\n';

    size_t firstd1 = 3;
    perm_t dummies1{1,2,3,4,5,6}, dummies1rc{3,4,1,2,5,6};

    cout << "    " << dummies1 << ", " << firstd1;
    moveDummyset(firstd1, dummies1);
    cout << " -> " << dummies1 << '\n';
    assert(dummies1 == dummies1rc);

    size_t firstd2 = 4;
    perm_t dummies2{1,2,3,4,5,6}, dummies2rc{4,3,2,1,6,5};

    cout << "    " << dummies2 << ", " << firstd2;
    moveDummyset(firstd2, dummies2);
    cout << " -> " << dummies2 << '\n';
    assert(dummies2 == dummies2rc);

    size_t firstd3 = 7;
    perm_t dummies3{1,2,3,4,5,6}, dummies3rc{1,2,3,4,5,6};

    cout << "    " << dummies3 << ", " << firstd3;
    moveDummyset(firstd3, dummies3);
    cout << " -> " << dummies3 << '\n';
    assert(dummies3 == dummies3rc);
}

void test_moveRepeatedset() {
    cout << "moveRepeatedset:" << '\n';

    size_t firstd1 = 3;
    perm_t repes1{1,2,3,4,5}, repes1rc{3,2,1,4,5};

    cout << "    " << repes1 << ", " << firstd1;
    moveRepeatedset(firstd1, repes1);
    cout << " -> " << repes1 << '\n';
    assert(repes1 == repes1rc);

    size_t firstd2 = 6;
    perm_t repes2{1,2,3,4,5}, repes2rc{1,2,3,4,5};

    cout << "    " << repes2 << ", " << firstd2;
    moveRepeatedset(firstd2, repes2);
    cout << " -> " << repes2 << '\n';
    assert(repes2 == repes2rc);
}

void test_SGSD() {
    cout << "SGSD:" << '\n';

    perm_t bD1, bD1rc{1, 3};
    gs_t KD1, KD1rc({{2,1,3,4,5}, {1,2,5,4,3}});
    perm_t vds1{2}, dummies1{1, 2};
    int mQ1[] = {1};
    size_t n1 = 5;
    perm_t vrs1{2}, repes1{3, 5};
    size_t firstd1 = 1;

    cout << "    dummies1: " << dummies1 << ", sym1: " << mQ1[0]
        << ", repes1: " << repes1 << ", firstd1: " << firstd1 << '\n';
    SGSD(bD1, KD1, dummies1, repes1, firstd1, vds1, mQ1, vrs1, n1);
    cout << "        -> <" << bD1 << ", " << KD1 << ">" << '\n';
    assert(bD1 == bD1rc);
    assert(KD1 == KD1rc);
}

/***** mode 6 *****/

void test_dropDummyset() {
    cout << "dropDummyset:" << '\n';

    size_t firstd1 = 1;
    perm_t vds1{6}, dummies1{1, 2, 3, 4, 5, 6}, dummies1rc{3, 4, 5, 6};

    cout << "    " << vds1 << ", " << dummies1 << ", " << firstd1;
    dropDummyset(firstd1, vds1, dummies1);
    cout << " -> " << dummies1 << '\n';
    assert(dummies1 == dummies1rc);

    size_t firstd9 = 3;
    perm_t vds9{6}, dummies9{3, 6, 5, 8, 4, 7}, dummies9rc{5, 8, 4, 7};

    cout << "    " << vds9 << ", " << dummies9 << ", " << firstd9;
    dropDummyset(firstd9, vds9, dummies9);
    cout << " -> " << dummies9 << '\n';
    assert(dummies9 == dummies9rc);

    firstd9 = 8;
    cout << "    " << vds9 << ", " << dummies9 << ", " << firstd9;
    dropDummyset(firstd9, vds9, dummies9);
    cout << " -> " << dummies9 << '\n';
    assert(dummies9 == dummies9rc);

    firstd9 = 4;
    cout << "    " << vds9 << ", " << dummies9 << ", " << firstd9;
    dropDummyset(firstd9, vds9, dummies9);
    cout << " -> " << dummies9 << '\n';
    assert(dummies9 == dummies9rc);

    firstd9 = 5;
    cout << "    " << vds9 << ", " << dummies9 << ", " << firstd9;
    dropDummyset(firstd9, vds9, dummies9);
    cout << " -> " << dummies9 << '\n';
    assert(dummies9 == perm_t({ 4,7 }));
}

void test_dropRepeatedset() {
    cout << "dropRepeatedset:" << '\n';

    size_t firstd1 = 1;
    perm_t vrs1{5}, repes1{1,2,3,4,5}, repes1rc{2,3,4,5};

    cout << "    " << repes1 << ", " << firstd1;
    dropRepeatedset(firstd1, vrs1, repes1);
    cout << " -> " << repes1 << '\n';
    assert(repes1 == repes1rc);
}

void test_double_coset_rep() {
    cout << "double_coset_rep:" << '\n';

    perm_t g1, base1, vds1, dummies1, vrs1, repes1, dcr1;
    gs_t GS1;
    size_t n1 = 0;
    int mQ1[] = {1};

    cout << "    g = " << g1 << ", <" << base1 << ", " << GS1
        << ">, dummies = " << dummies1 << ", sym: " << mQ1[0];
    dcr1 = double_coset_rep(g1, n1, base1, GS1, vds1, dummies1, mQ1, vrs1, repes1);
    cout << '\n' << "        -> " << dcr1 << '\n';
    assert(dcr1 == g1);

    perm_t g2{2,1,3,4}, g2rc{1,2,3,4}, base2, vds2{2}, dummies2{1,2}, vrs2, repes2, dcr2;
    gs_t GS2;
    size_t n2 = 4;
    int mQ2[] = {1};

    cout << "    g = " << g2 << ", <" << base2 << ", " << GS2
        << ">, dummies = " << dummies2 << ", sym: " << mQ2[0];
    dcr2 = double_coset_rep(g2, n2, base2, GS2, vds2, dummies2, mQ2, vrs2, repes2);
    cout << '\n' << "        -> " << dcr2 << '\n';
    assert(dcr2 == g2rc);

    perm_t g3{2,1,3,4}, g3rc{1,2,3,4}, base3{1}, vds3{2}, dummies3{1,2}, vrs3, repes3, dcr3;
    gs_t GS3({{2,1,3,4}});
    size_t n3 = 4;
    int mQ3[] = {1};

    cout << "    g = " << g3 << ", <" << base3 << ", " << GS3
        << ">, dummies = " << dummies3 << ", sym: " << mQ3[0];
    dcr3 = double_coset_rep(g3, n3, base3, GS3, vds3, dummies3, mQ3, vrs3, repes3);
    cout << '\n' << "        -> " << dcr3 << '\n';
    assert(dcr3 == g3rc);

    perm_t g4{2,1,3,4}, g4rc{0,0,0,0}, base4, vds4{2}, dummies4{1,2}, vrs4, repes4, dcr4;
    gs_t GS4({{2,1,4,3}});
    size_t n4 = 4;
    int mQ4[] = {1};

    cout << "    g = " << g4 << ", <" << base4 << ", " << GS4
        << ">, dummies = " << dummies4 << ", sym: " << mQ4[0];
    dcr4 = double_coset_rep(g4, n4, base4, GS4, vds4, dummies4, mQ4, vrs4, repes4);
    cout << '\n' << "        -> " << dcr4 << '\n';
    assert(dcr4 == g4rc);

    perm_t g5{3,4,1,2,5,6}, g5rc{0,0,0,0,0,0}, base5, vds5{2}, dummies5{3,4}, vrs5, repes5, dcr5;
    gs_t GS5({{2,1,3,4,6,5}});
    size_t n5 = 6;
    int mQ5[] = {1};

    cout << "    g = " << g5 << ", <" << base5 << ", " << GS5
        << ">, dummies = " << dummies5 << ", sym: " << mQ5[0];
    dcr5 = double_coset_rep(g5, n5, base5, GS5, vds5, dummies5, mQ5, vrs5, repes5);
    cout << '\n' << "        -> " << dcr5 << '\n';
    assert(dcr5 == g5rc);

    perm_t g6{3,1,4,2,5,6}, g6rc{1,3,2,4,5,6}, base6{1,2,3},
           vds6{4}, dummies6{1,2,3,4}, vrs6, repes6, dcr6;
    gs_t GS6({{1,2,4,3,5,6}});
    size_t n6 = 6;
    int mQ6[] = {1};

    cout << "    g = " << g6 << ", <" << base6 << ", " << GS6
        << ">, dummies = " << dummies6 << ", sym: " << mQ6[0];
    dcr6 = double_coset_rep(g6, n6, base6, GS6, vds6, dummies6, mQ6, vrs6, repes6);
    cout << '\n' << "        -> " << dcr6 << '\n';
    assert(dcr6 == g6rc);

    perm_t g7{1,3,4,2,5,6}, g7rc{1,3,2,4,6,5}, base7{1},
           vds7{4}, dummies7{1,2,3,4}, vrs7, repes7, dcr7;
    gs_t GS7({{1,2,4,3,6,5}});
    size_t n7 = 6;
    int mQ7[] = {1};

    cout << "    g = " << g7 << ", <" << base7 << ", " << GS7
        << ">, dummies = " << dummies7 << ", sym: " << mQ7[0];
    dcr7 = double_coset_rep(g7, n7, base7, GS7, vds7, dummies7, mQ7, vrs7, repes7);
    cout << '\n' << "        -> " << dcr7 << '\n';
    assert(dcr7 == g7rc);

    perm_t g8{1,3,2,4,5,6}, g8rc{1,4,3,2,6,5}, base8{1,3},
           vds8{4}, dummies8{1,2,3,4}, vrs8, repes8, dcr8;
    gs_t GS8({{3,4,1,2,5,6}, {2,1,3,4,6,5}, {1,2,4,3,6,5}});
    size_t n8 = 6;
    int mQ8[] = {1};

    cout << "    g = " << g8 << ", <" << base8 << ", " << GS8
        << ">, dummies = " << dummies8 << ", sym: " << mQ8[0];
    dcr8 = double_coset_rep(g8, n8, base8, GS8, vds8, dummies8, mQ8, vrs8, repes8);
    cout << '\n' << "        -> " << dcr8 << '\n';
    assert(dcr8 == g8rc);

    perm_t g9{5,7,3,4,1,2,8,6,9,10}, g9rc{3,4,5,6,1,2,7,8,9,10}, base9{1,2,3,4,5,6,7,8},
           vds9{6}, dummies9{5,8,3,6,4,7}, vrs9, repes9, dcr9;
    gs_t GS9({
        {2,1,3,4,5,6,7,8,9,10},
        {1,2,4,3,5,6,7,8,9,10},
        {1,2,3,4,6,5,7,8,9,10},
        {3,4,1,2,5,6,7,8,9,10}});
    size_t n9 = 10;
    int mQ9[] = {1};

    cout << "    g = " << g9 << ", <" << base9 << ", " << GS9
        << ">, dummies = " << dummies9 << ", sym: " << mQ9[0];
    dcr9 = double_coset_rep(g9, n9, base9, GS9, vds9, dummies9, mQ9, vrs9, repes9);
    cout << '\n' << "        -> " << dcr9 << '\n';
    assert(dcr9 == g9rc);
}

/***** mode 7 *****/

void test_canonical_perm_ext() {
    cout << "canonical_perm:" << '\n';

    perm_t perm1, cr_perm1, base1{1,3};
    gs_t GS1;
    size_t n1 = 0;
    perm_t frees1, vds1, dummies1, vrs1, repes1;
    int mQ1[] = {1};

    cout << "    1: " << perm1 << ", <" << base1 << ", " << GS1 << ">, sym = " << mQ1[0] << '\n';
    cr_perm1 = canonical_perm_ext(perm1, n1, base1, GS1, frees1, vds1, dummies1, mQ1, vrs1, repes1);
    cout << "       -> " << cr_perm1 << '\n';
    assert(cr_perm1 == perm1);

    perm_t perm2{6,5,4,3,2,1,7,8}, perm2rc{6,5,1,3,2,4,8,7}, base2{1,2,3,4,5,6}, frees2{1,2,3,4,5,6}, cr_perm2;
    gs_t GS2({{1,2,5,4,3,6,8,7}, {1,2,3,4,6,5,8,7}});
    size_t n2 = 8;
    perm_t vds2, dummies2, vrs2, repes2;
    int mQ2[] = {1};

    cout << "    2: " << perm2 << ", <" << base2 << ", " << GS2 << ">, sym = " << mQ2[0] << '\n';
    cr_perm2 = canonical_perm_ext(perm2, n2, base2, GS2, frees2, vds2, dummies2, mQ2, vrs2, repes2);
    cout << "       -> " << cr_perm2 << '\n';
    assert(cr_perm2 == perm2rc);

    perm_t perm3{2,1,4,3,5,6}, perm3rc{1,2,3,4,5,6}, base3{1,2,3,4},
           vds3, dummies3, vrs3, repes3, frees3{1,2,3,4}, cr_perm3;
    gs_t GS3({{4,3,2,1,5,6}, {3,4,2,1,6,5}, {1,2,4,3,6,5}});
    size_t n3 = 6;
    int mQ3[] = {1};

    cout << "    3: " << perm3 << ", <" << base3 << ", " << GS3 << ">, sym = " << mQ3[0] << '\n';
    cr_perm3 = canonical_perm_ext(perm3, n3, base3, GS3, frees3, vds3, dummies3, mQ3, vrs3, repes3);
    cout << "       -> " << cr_perm3 << '\n';
    assert(cr_perm3 == perm3rc);

    perm_t perm4{5,7,3,4,1,2,8,6,9,10}, perm4rc{3,4,5,6,1,2,7,8,9,10}, base4{1,2,3,4,5,6,7,8},
           frees4{1,2}, vds4{6}, dummies4{5,8,3,6,4,7}, vrs4, repes4, cr_perm4;
    gs_t GS4({
        {2,1,3,4,5,6,7,8,9,10},
        {1,2,4,3,5,6,7,8,9,10},
        {1,2,3,4,6,5,7,8,9,10},
        {3,4,1,2,5,6,7,8,9,10}});
    size_t n4 = 10;
    int mQ4[] = {1};

    cout << "    4: " << perm4 << ", <" << base4 << ", " << GS4 << ">, sym = " << mQ4[0] << '\n';
    cr_perm4 = canonical_perm_ext(perm4, n4, base4, GS4, frees4, vds4, dummies4, mQ4, vrs4, repes4);
    cout << "       -> " << cr_perm4 << '\n';
    assert(cr_perm4 == perm4rc);

    perm_t perm5{12,2,1,5,6,8,3,9,10,7,4,11,13,14}, perm5rc{1,5,2,12,3,9,6,8,4,11,7,10,13,14},
           base5{1,2,3,4,5,6,7,8,9,10,11,12}, frees5{1,2,3,4,5,6,7,8,9,10,11,12},
           cr_perm5, vds5, dummies5, vrs5, repes5;
    gs_t GS5({
        {3,4,1,2,5,6,7,8,9,10,11,12,13,14},
        {2,1,3,4,5,6,7,8,9,10,11,12,14,13},
        {1,2,4,3,5,6,7,8,9,10,11,12,14,13},
        {1,2,3,4,9,10,11,12,5,6,7,8,13,14},
        {1,2,3,4,7,8,5,6,9,10,11,12,13,14},
        {1,2,3,4,6,5,7,8,9,10,11,12,14,13},
        {1,2,3,4,5,6,8,7,9,10,11,12,14,13},
        {1,2,3,4,5,6,7,8,11,12,9,10,13,14},
        {1,2,3,4,5,6,7,8,10,9,11,12,14,13},
        {1,2,3,4,5,6,7,8,9,10,12,11,14,13}});
    size_t n5 = 14;
    int mQ5[] = {1};

    cout << "    5: " << perm5 << ", <" << base5 << ", " << GS5 << ">, sym = " << mQ5[0] << '\n';
    cr_perm5 = canonical_perm_ext(perm5, n5, base5, GS5, frees5, vds5, dummies5, mQ5, vrs5, repes5);
    cout << "       -> " << cr_perm5 << '\n';
    assert(cr_perm5 == perm5rc);

    perm_t perm6{12,2,1,5,6,8,3,9,10,7,4,11,13,14}, perm6rc{1,3,2,5,4,7,9,11,6,10,8,12,14,13},
           base6{1,2,3,4,5,6,7,8,9,10,11,12}, frees6{1,2}, vds6{10}, dummies6{3,4,5,6,7,8,9,10,11,12},
           cr_perm6, vrs6, repes6;
    gs_t GS6({
        {3,4,1,2,5,6,7,8,9,10,11,12,13,14},
        {2,1,3,4,5,6,7,8,9,10,11,12,14,13},
        {1,2,4,3,5,6,7,8,9,10,11,12,14,13},
        {1,2,3,4,9,10,11,12,5,6,7,8,13,14},
        {1,2,3,4,7,8,5,6,9,10,11,12,13,14},
        {1,2,3,4,6,5,7,8,9,10,11,12,14,13},
        {1,2,3,4,5,6,8,7,9,10,11,12,14,13},
        {1,2,3,4,5,6,7,8,11,12,9,10,13,14},
        {1,2,3,4,5,6,7,8,10,9,11,12,14,13},
        {1,2,3,4,5,6,7,8,9,10,12,11,14,13}});
    size_t n6 = 14;
    int mQ6[] = {1};

    cout << "    6: " << perm6 << ", <" << base6 << ", " << GS6 << ">, sym = " << mQ6[0] << '\n';
    cr_perm6 = canonical_perm_ext(perm6, n6, base6, GS6, frees6, vds6, dummies6, mQ6, vrs6, repes6);
    cout << "       -> " << cr_perm6 << '\n';
    assert(cr_perm6 == perm6rc);

    perm_t perm7{2,1,3,4}, perm7rc{0,0,0,0}, base7{1,2}, frees7,
           vds7{2}, dummies7{2,1}, cr_perm7, vrs7, repes7;
    gs_t GS7({{2,1,4,3}});
    size_t n7 = 4;
    int mQ7[] = {1};

    cout << "    7: " << perm7 << ", <" << base7 << ", " << GS7 << ">, sym = " << mQ7[0] << '\n';
    cr_perm7 = canonical_perm_ext(perm7, n7, base7, GS7, frees7, vds7, dummies7, mQ7, vrs7, repes7);
    cout << "       -> " << cr_perm7 << '\n';
    assert(cr_perm7 == perm7rc);

    perm_t perm8{3,4,1,2,5,6}, perm8rc{0,0,0,0,0,0}, base8{1,2,3,4}, frees8{1,2},
           vds8{2}, dummies8{3,4}, cr_perm8, vrs8, repes8;
    gs_t GS8({{2,1,3,4,6,5}, {1,2,4,3,6,5}, {3,4,1,2,5,6}});
    size_t n8 = 6;
    int mQ8[] = {1};

    cout << "    8: " << perm8 << ", <" << base8 << ", " << GS8 << ">, sym = " << mQ8[0] << '\n';
    cr_perm8 = canonical_perm_ext(perm8, n8, base8, GS8, frees8, vds8, dummies8, mQ8, vrs8, repes8);
    cout << "       -> " << cr_perm8 << '\n';
    assert(cr_perm8 == perm8rc);

    perm_t perm9{1,3,2,4,5,6}, perm9rc{1,4,3,2,6,5}, perm90rc{1,3,2,4,5,6}, base9{1,3},
           vds9{4}, dummies9{1,2,3,4}, cr_perm9, frees9, vrs9, repes9;
    gs_t GS9({{2,1,3,4,6,5}, {1,2,4,3,6,5}, {3,4,1,2,5,6}});
    size_t n9 = 6;
    int mQ9[] = {1};

    cout << "    9: " << perm9 << ", <" << base9 << ", " << GS9 << ">, sym = " << mQ9[0] << '\n';
    cr_perm9 = canonical_perm_ext(perm9, n9, base9, GS9, frees9, vds9, dummies9, mQ9, vrs9, repes9);
    cout << "       -> " << cr_perm9 << '\n';
    assert(cr_perm9 == perm9rc);

    perm_t perm10{1, 2, 3, 4}, perm10rc{1, 2, 3, 4}, base10{1}, vds10{2},
           dummies10{1, 2}, cr_perm10, frees10, vrs10, repes10;
    gs_t GS10({{2,1,3,4}});
    size_t n10 = 4;
    int mQ10[] = {1};

    cout << "    10: " << perm10 << ", <" << base10 << ", " << GS10 << ">, sym = " << mQ10[0] << '\n';
    cr_perm10 = canonical_perm_ext(perm10, n10, base10, GS10, frees10, vds10, dummies10, mQ10, vrs10, repes10);
    cout << "        -> " << cr_perm10 << '\n';
    assert(cr_perm10 == perm10rc);
}

/*********************************************************************/
/************************* make_perm_group ***************************/
/*********************************************************************/

void test_memberq_gs() {
    perm_t perm1, perm2{2,1,5,4,3};
    gs_t GS1({{2,1,5,4,3}, {1,2,3,4,5}});

    cout << "memberq_gs:" << '\n';

    cout << "    " << GS1 << ", " << perm1
         << " -> " << std::boolalpha << memberq_gs(GS1, perm1) << '\n';
    assert(memberq_gs(GS1, perm1) == false);

    cout << "    " << GS1 << ", " << perm2
         << " -> " << std::boolalpha << memberq_gs(GS1, perm2) << '\n';
    assert(memberq_gs(GS1, perm2) == true);
}

// res = GS1 - GS2
static gs_t complement_gs(const gs_t& GS1, const gs_t& GS2) {
    gs_t dest;

    for (const auto& perm : GS1)
        if (!memberq_gs(GS2, perm)) dest.push_back(perm);

    return dest;
}

void test_make_perm_group() {
    cout << "make_perm_group:" << '\n';

    gs_t group;

    gs_t gs1;
    size_t n1 = 0;
    make_perm_group(group, gs1, n1);
    cout << "    " << gs1 << "\n    -> " << group << "\n\n";
    assert(group == gs1);

    gs_t gs2{{2,3,4,1}}, GS2rc{{1,2,3,4}, {2,3,4,1}, {3,4,1,2}, {4,1,2,3}};
    size_t n2 = 4;
    make_perm_group(group, gs2, n2);
    cout << "    " << gs2 << "\n    -> " << group << "\n\n";
    assert(group == GS2rc);

    gs_t gs3({{2,1,3,5,4}, {1,3,2,4,5}}),
         GS3rc{{1,2,3,4,5}, {2,1,3,5,4}, {1,3,2,4,5}, {3,1,2,5,4},
               {2,3,1,5,4}, {3,2,1,4,5}, {3,2,1,5,4}, {2,3,1,4,5},
               {3,1,2,4,5}, {1,3,2,5,4}, {2,1,3,4,5}, {1,2,3,5,4}};
    size_t n3 = 5;
    make_perm_group(group, gs3, n3);
    cout << "    " << gs3 << "\n    -> " << group << "\n\n";
    assert(complement_gs(group, GS3rc) == gs_t());

    gs_t gs4({{4,1,2,3}, {2,1,3,4}}),
         GS4rc{{1,2,3,4}, {1,2,4,3}, {1,3,2,4}, {1,3,4,2},
               {1,4,2,3}, {1,4,3,2}, {2,1,3,4}, {2,1,4,3},
               {2,3,1,4}, {2,3,4,1}, {2,4,1,3}, {2,4,3,1},
               {3,1,2,4}, {3,1,4,2}, {3,2,1,4}, {3,2,4,1},
               {3,4,1,2}, {3,4,2,1}, {4,1,2,3}, {4,1,3,2},
               {4,2,1,3}, {4,2,3,1}, {4,3,1,2}, {4,3,2,1}};
    size_t n4 = 4;
    make_perm_group(group, gs4, n4);
    cout << "    " << gs4 << "\n    -> " << group << "\n\n";
    assert(complement_gs(group, GS4rc) == gs_t());

    gs_t gs5({{5,1,2,3,4},{2,1,3,4,5}});
    size_t n5 = 5;
    make_perm_group(group, gs5, n5);
    cout << "    " << gs5 << "\n    -> " << group << ", size: " << group.size() << "\n\n";
    assert(group.size() == 120);
}

#include <omp.h>
void bench_test() {
    double start1 = omp_get_wtime();

    for (int i = 0; i < 1000; ++i)
        test_SGSD();

    double end1 = omp_get_wtime();
    cout << "elapsed time = " << end1 - start1 << " sec" << "\n\n";
}

/**********************************************************************/
int main() {
    cout << "**********************************************************\n";
    test_complement_vec();
    test_memberq_vec();
    test_intersection_vec();
    test_join_vec();
    test_position_vec();
    test_range_vec();
    test_sort_vec();
    test_take_vec();

    cout << "**********************************************************\n";
    test_product_perm();
    test_inverse_perm();
    test_onpoint();
    test_sortB();

    cout << "**********************************************************\n";
    test_orbit();
    test_schreier_orbit();
    test_schreier_vector();
    test_trace_schreier();

    cout << "**********************************************************\n";
    test_stabilizer();
    test_right_coset_rep();

    cout << "**********************************************************\n";
    test_SGSofDummyset();
    test_SGSofRepeatedset();
    test_moveDummyset();
    test_moveRepeatedset();
    test_SGSD();

    cout << "**********************************************************\n";
    test_dropDummyset();
    test_dropRepeatedset();
    test_double_coset_rep();
    test_canonical_perm_ext();

    cout << "**********************************************************\n";
    test_memberq_gs();
    test_make_perm_group();

//    bench_test();

    return 0;
}
