(* Robertson-Walker Metric *)

(* Rules for components simplification *)
CsimplifyRules = {}

(* Options for MMA commands in Csimplify *)
SetOptions[Expand, Trig -> False]

(* Commands for components simplication *)
Csimplify[expr_] := Simplify @ Expand[expr //. CsimplifyRules]

(* SpaceTime Metric *)
Table[Metricg[-i,-j] = 0, {i, 4}, {j, 4}]
Metricg[-1,-1] = -1
Metricg[-2,-2] = a[\[Tau]]^2 / (1 - \[Kappa] r^2)
Metricg[-3,-3] = a[\[Tau]]^2 * r^2
Metricg[-4,-4] = a[\[Tau]]^2 * r^2 * Sin[\[Theta]]^2

(* Initialize for component calculations *)
Print["Coordinate System = ", {\[Tau], r, \[Theta], \[Phi]}]
InitCTensor[{\[Tau], r, \[Theta], \[Phi]},            (* coordinate systems *)
            Table[Metricg[-i,-j], {i, 4}, {j, 4}],    (* metric *)
            RicciCD -> True]                          (* options for InitCTensor *)