(* :Title: mTensor *)
(* :Author: Dal-Ho Park *)
(* :Summary: mTensor for manipulating tensors in Mathematica *)
(* :Package Version: 2020.12 *)
(* :Mathematica Version: 10.4 *)

(********************************************************************)
BeginPackage["mTensor`", {"mTensor`xPermML`"}]

(* 디버깅 용도 *)
$dndn::usage = ""
$upup::usage = ""
$dnup::usage = ""
$updn::usage = ""

(***************************** Utilities ****************************)

FreePatternQ::usage     = ""
PositiveIntegerQ::usage = ""
SymbolJoin::usage       = ""

(* 함수의 옵션 용도 *)
CovDs::usage   = ""
HeadQs::usage  = ""
IndexQs::usage = ""

xSlot::usage = ""  (* for FreePatternQ *)

(***** messages *****)
Msg::err  = "`1` `2` `3` `4`"
Msg::warn = "`1` `2` `3` `4`"
Msg::note = "`1` `2` `3` `4` `5`"
General::invalid = "`1` is not a valid `2`.";

(****************************** Indices *****************************)

DnIndexQ::usage = "DnIndexQ[index]"
UpIndexQ::usage = "UpIndexQ[index]"

ComponentIndexQ::usage = "ComponentIndexQ[index]"
DummyIndexQ::usage     = "DummyIndexQ[index]"
RegularIndexQ::usage   = "RegularIndexQ[index]"

DefineKind::usage = "DefineKind[symbL, kind]"
KindIndexQ::usage = "KindIndexQ[kind]"
RemoveKind::usage = "RemoveKind[kind]"

AddIndices::usage  = "AddIndices[num, kind]"
SetIndices::usage  = "SetIndices[charL, kind]"
ShowIndices::usage = "ShowIndices[kind]"

FlipIndex::usage       = "FlipIndex[index]"
IndexOrderedQ::usage   = "IndexOrderedQ[indexL]"
IndexSort::usage       = "IndexSort[indexL]"
PairIndexQ::usage      = "PairIndexQ[index1, index2]"
TensorialIndexQ::usage = "TensorialIndexQ[index]"

Dummy::usage     = "Dummy[kind]"
DummyPair::usage = "DummyPair[kind]"
TakePairs::usage = "TakePairs[indexL, <IndexQs>]"
ToDnIndex::usage = "ToDnIndex[index]"
ToUpIndex::usage = "ToUpIndex[index]"

ValidIndexQ::usage   = "ValidIndexQ[index, <kind>]"
ValidIndicesQ::usage = "ValidIndicesQ[indexL, <kind>]"

(***** Exported Symbols *****)
DefaultKind::usage = ""
Latin::usage       = ""
Zero::usage        = ""

(********************** Defining IndexedObject **********************)

(* Objects *)
RemoveObject::usage     = "RemoveObject[oName]"
ObjectQ::usage          = "ObjectQ[oName]"
IndexedObjectQ::usage   = "IndexedObjectQ[oName]"
IndexedOperandQ::usage  = "IndexedOperandQ[oName]"
IndexedTensorQ::usage   = "IndexedTensorQ[oName]"
IndexedFormQ::usage     = "IndexedFormQ[oName]"      (* cf: vectorNameQ[] *)
IndexedOperatorQ::usage = "IndexedOperatorQ[opName]"
ScalarFunctionQ::usage  = "ScalarFunctionQ[sfName]"

(* Define Tensors *)
Tdefine::usage = "Tdefine[oName[indices], <prtStr>, permStr]"
GetRank::usage = "GetRank[oName]"
KindOf::usage  = "KindOf[name, <arg>]"

AllPermutations::usage = "AllPermutations[permS]"
GStoString::usage      = "GStoString[GS, <len>]"

(* Index Symmetries *)
GetSymmetry::usage = "GetSymmetry[oName]"
SetSymmetry::usage = "SetSymmetry[oName, permS]"

(***** Exported Symbols *****)
(* Operator Types *)
CD::usage = "CD[index, expr]"
LD::usage = "LD[v, expr]"
XD::usage = "XD[expr]"
XP::usage = "XP[args,..]"

(* Wrappers *)
ErrorT::usage  = ""
Tscalar::usage = ""

(***************** Operations on Indexed Expressions ****************)

(* Utilities for indexed exprs *)
NoIndexQ::usage = "NoIndexQ[expr, <opts>]"

(* Reordering indices of IndexedObject *)
AntisymmetrizeIndices::usage = "AntisymmetrizeIndices[{a,..}, expr, <HeadQs>]"
SymmetrizeIndices::usage     = "SymmetrizeIndices[{a,..}, expr, <HeadQs>]"

(* Dummy Operations *)
Dum::usage          = "Dum[expr, <opts>]"
DumFresh::usage     = "DumFresh[expr, <opts>]"
ResetDummies::usage = "ResetDummies[expr, <opts>]"
SumDum::usage       = "SumDum[args, expr, <opts>]"

(* RuleUnique *)
RuleUnique::usage = "RuleUnique[lhs, rhs, <cond>]"
DefUnique::usage  = "DefUnique[lhs, rhs, <cond>]"

(* SyntaxCheck *)
SyntaxCheck::usage = "SyntaxCheck[expr, <HeadQs>]"

(* Flags *)
AutoFlag::usage         = ""
MarkErrorFlag::usage    = ""
ResetDummiesFlag::usage = ""
SyntaxCheckFlag::usage  = ""

(********************** Predefined Structures ***********************)

(***** Covariant Derivatives *****)
DerivativeOperatorQ::usage      = "DerivativeOperatorQ[opName]"
DefineDerivativeOperator::usage = "DefineDerivativeOperator[covD, prtStr, <kind>, <opts>]"
RemoveDerivativeOperator::usage = "RemoveDerivativeOperator[covD]"

TorsionFreeQ::usage = ""  (* CovD's properties *)

GammaCD::usage     = ""
Ricci::usage       = ""
RicciCD::usage     = ""
Riemann::usage     = ""
RiemannCD::usage   = ""
Scalar::usage      = ""
ScalarCD::usage    = ""
Weyl::usage        = ""
WeylCD::usage      = ""

Kdelta::usage     = ""  (* any kind *)
Epsilon::usage    = ""  (* default kind *)
Structuref::usage = ""
Torsion::usage    = ""

(***** Metrics *****)
MetricQ::usage      = "MetricQ[metric]"
DefineMetric::usage = "DefineMetric[metric, <prtStr>, <kind>, <sym>]"
RemoveMetric::usage = "RemoveMetricQ[metric]"

MakeMetricConnection::usage  = "MakeMetricConnection[covD, metric]"
ClearMetricConnection::usage = "ClearMetricConnection[covD, metric]"

Metricg::usage = ""  (* DefaultKind *)

(***** kind's properties *****)
CoordinateBasisQ::usage = ""
MetricSpaceQ::usage     = ""
GetDimension::usage     = ""
GetEpsilon::usage       = ""
GetMetric::usage        = ""
GetSignature::usage     = ""
GetStructuref::usage    = ""
GetTorsion::usage       = ""

(***** Set DefaultKind, Dimension, Signature, and Coordinates *****)

SetDefaultKind::usage = "SetDefaultKind[kind]"

SetDimension::usage   = "SetDimension[dim, <kind>]"
ClearDimension::usage = "ClearDimension[<kind>]"

SetSignature::usage   = "SetSignature[sig, <kind>]"
ClearSignature::usage = "ClearSignature[<kind>]"

SetCoordinates::usage   = "SetCoordinates[coSys, <kind>]"
ClearCoordinates::usage = "ClearCoordinates[<kind>]"

Status::usage = "Status[<kind>]"

(***** Predefined Tensorial Operators *****)

(* Defined Operators *)
BD::usage = "BD[aIndex, expr]"

(***** On/Off Flags *****)

CoordinateBasisFlag::usage = ""
EvaluateBDFlag::usage      = ""
KdeltaFlag::usage          = ""
MetricgFlag::usage         = ""

(***** Absorb and PutMetric *****)

Absorb::usage  = "Absorb[expr, metric, <IndexQs>, <HeadQs>, <CovDs>]"
Absorbg::usage = "Absorbg[expr, <IndexQs>, <HeadQs>, <CovDs>]"

PutMetric::usage = "PutMetric[expr, index, <opts>]"
SeparateMetric::usage = "SeparateMetric[expr, <opts>]"

(***** Hodge Dual *****)

DualStar::usage = "DualStar[term, <indexL>]"

(************************* Differential Form ************************)

Fdefine::usage   = "Fdefine[fName, <prtStr>, nDegree, <permStr>]"

XP::usage = "XP[args,..]"
IP::usage = "IP[vName, pForm]"
HodgeStar::usage = "HodgeStar[pForm]"
CoXD::usage      = "CoXD[pForm]"

CoXDRule::usage   = ""
LDtoXDRule::usage = ""

XDtoCDfrag::usage = ""

ApplyXD::usage     = ""
CollectForm::usage = "CollectForm[expr]"
DegreeForm::usage  = "DegreeForm[expr]"
ZeroDegreeQ::usage = "ZeroDegreeQ[expr]"
ToTensor::usage    = "ToTensor[expr, <indexL>]"

CoordRep::usage = ""

(**************************** Variation *****************************)

VD::usage = "VD[arg, expr]"

(* VD options *)
ByPartsVD::usage     = ""
IndependentVD::usage = ""

(*************************** ToCanonical ****************************)

ToCanonical::usage = "ToCanonical[expr]"

(***** Exported Symbols *****)
xCommutingObjects::usage = ""
xObject::usage = ""
xNoIndex::usage = ""
xSlot::usage = ""
xSymmetry::usage = ""
xTensorTimes::usage = ""
xTTimes::usage = ""

(**************************** Tsimplify *****************************)

DnUpPair::usage = "DnUpPair[expr, <opts>]"
UpDnPair::usage = "UpDnPair[expr, <opts>]"

BDinvgRule::usage         = "BDinvgRule[<metric>]"
EpsilonProductRule::usage = "EpsilonProductRule[<kind>]"
KdeltaSumRule::usage      = "KdeltaSumRule[<kind>]"

TindexSort::usage = "TindexSort[expr]"  (* xSymmetryOf, xSort *)
Tsimplify::usage  = "Tsimplify[expr]"   (* metricStatesOf, xSymmetryOf, xSort, flattenObject *)
TsimplifyPatternMatching::usage = "TsimplifyPatternMatching[expr]"  (* xSymmetryOf, xSort *)

(********************************************************************)
Begin["`Private`"]

(*************************** IndexNotation **************************)
<< mTensor`IndexNotation`

(****************************** Tensor ******************************)
<< mTensor`Tensor`
<< mTensor`DiffForm`
<< mTensor`Variation`    (* Experimental *)

(******************** ToCanonical and Tsimplify *********************)
<< mTensor`xToCanonical`
<< mTensor`Tsimplify`

(**************************** TensorGRG *****************************)
<< mTensor`TensorGRG`
<< mTensor`Hypersurface` (* Experimental *)

(**************************** TensorFlat ****************************)
<< mTensor`TensorFlat`   (* Experimental *)

(****************************** CTensor *****************************)
<< mTensor`CTensor`
<< mTensor`CTensorNT`    (* Experimental *)

(********************************************************************)

End[]

EndPackage[]
