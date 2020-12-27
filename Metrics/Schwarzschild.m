(* Schwarzschild Metric *)

(* Rules for components simplification *)
CsimplifyRules = {Cos[\[Theta]]^2 -> 1 - Sin[\[Theta]]^2,
                  Cos[\[Theta]]^4 -> (1- Sin[\[Theta]]^2)^2}

(* Options for MMA commands in Csimplify *)
SetOptions[Expand, Trig -> False]
SetOptions[Together, Trig -> True]

(* Commands for components simplication *)
Csimplify[expr_] := Together @ Expand[expr //. CsimplifyRules]

(* SpaceTime Metric *)
SetAttributes[G, Constant]
SetAttributes[M, Constant]

Table[Metricg[-i,-j] = 0, {i, 4}, {j, 4}]
Metricg[-1,-1] = -(1 - (2*G*M)/r)
Metricg[-2,-2] = 1 / (1 - (2*G*M)/r)
Metricg[-3,-3] = r^2
Metricg[-4,-4] = r^2 Sin[\[Theta]]^2

(* Initialize for component calculations *)
Print["Coordinate System = ", {t, r, \[Theta], \[Phi]}]
InitCTensor[{t, r, \[Theta], \[Phi]},                 (* coordinate systems *)
            Table[Metricg[-i,-j], {i, 4}, {j, 4}],    (* metric *)
            RicciCD -> True]                          (* options for InitCTensor *)