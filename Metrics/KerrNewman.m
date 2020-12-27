(* Kerr-Newman Metric *)

(* Rules for components simplification *)
CsimplifyRules = {}

(* Options for MMA commands in Csimplify *)
SetOptions[Expand, Trig -> False]

(* Commands for components simplication *)
Csimplify[expr_] := Simplify @ Expand[expr //. CsimplifyRules]

(* SpaceTime Metric *)
SetAttributes[a, Constant]
SetAttributes[M, Constant]
SetAttributes[Q, Constant]
\[CapitalDelta] = r^2 - 2*M*r + a^2 + Q^2
\[CapitalSigma] = r^2 + a^2 * Cos[\[Theta]]^2

Table[Metricg[-i,-j] = 0, {i, 4}, {j, 4}]
Metricg[-1,-1] = -(\[CapitalDelta] - a^2 * Sin[\[Theta]]^2) / \[CapitalSigma]
Metricg[-1,-4] = -a * Sin[\[Theta]]^2 * (r^2 + a^2 - \[CapitalDelta]) / \[CapitalSigma]
Metricg[-2,-2] = \[CapitalSigma] / \[CapitalDelta]
Metricg[-3,-3] = \[CapitalSigma]
Metricg[-4,-4] = ((r^2 + a^2)^2 - \[CapitalDelta] * a^2 * Sin[\[Theta]]^2) \
                 * Sin[\[Theta]]^2 / \[CapitalSigma]
Table[Metricg[-i,-j] = Metricg[-j,-i], {i,4},{j,i}]

(* Initialize for component calculations *)
Print["Coordinate System = ", {t, r, \[Theta], \[Phi]}] (* Message *)
InitCTensor[{t, r, \[Theta], \[Phi]},                   (* coordinate systems *)
            Table[Metricg[-i,-j], {i, 4}, {j, 4}],      (* metric *)
            Verbose -> True, GammaCD -> True]           (* options for InitCTensor *)
