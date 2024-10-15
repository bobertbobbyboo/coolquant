(* ::Package:: *)

BeginPackage["CoolQuant`"]


VARASSUME = {m\[Element]Reals, m>0, \[Omega]\[Element]Reals, \[Omega]>0, \[HBar]\[Element]Reals, \[HBar]>0, x\[Element]Reals, p\[Element]Reals};
$Assumptions = If[$Assumptions===True, VARASSUME, Join[$Assumptions, VARASSUME]];
SetAttributes[{m, \[Omega], \[HBar]}, Constant]

(* Parameter Conventions:
	a, b etc. scalars
	\[Alpha], \[Beta] etc. general objects
	Bra[{g}], Ket[{f}] bra-ket
	Overscript[O, ^], Overscript[Q, ^] operators
	fx unevaluated expressions
*)


(* Safety Off *)
(* we are apparently performing surgery on these operations. *)
(* IMPORTANT: lower definitions overwrite higher definitions given same Tag. *)
(* reprotect at the end!! *)
PATIENTS = {Plus, Times, CenterDot, NonCommutativeMultiply};
Unprotect @@ PATIENTS


(* Quantum Objects (operators, bras, kets) *)
(* _h is anything with the head h, a_. denotes optional pattern *)
OperatorQ[expr_] := MatchQ[Distribute @ expr, a_. \[Alpha]_ ~QDot~ Q_?OperatorQ + \[Beta]_.] \
					\[Or] MatchQ[Distribute @ expr, a_. Q_?OperatorQ ~QDot~ \[Alpha]_ + \[Beta]_.] \
					\[Or] MatchQ[Distribute @ expr, a_. _Operator + \[Beta]_.]
KetQ[expr_] := MatchQ[expr, \[Alpha]_ ~QDot~ _Ket] \[Or] MatchQ[expr, a_. _Ket]
BraQ[expr_] := MatchQ[expr, _Bra ~QDot~ \[Alpha]_] \[Or] MatchQ[expr, a_. _Bra]
QObjQ[expr_] := OperatorQ[expr] \[Or] KetQ[expr] \[Or] BraQ[expr]


(* Operators *)
Operator = OverHat;
\!\(\*OverscriptBox[\(x\), \(^\)]\)[fx_] := x fx
\!\(\*OverscriptBox[\(p\), \(^\)]\)[fx_] := -I \[HBar] \!\(
\*SubscriptBox[\(\[PartialD]\), \(x\)]fx\)


(* Bra-ket Notation *)
Ket/: Ket[{f_}]\[ConjugateTranspose] := Bra[{f}]
Bra/: Bra[{f_}]\[ConjugateTranspose] := Ket[{f}]


(* Dot Operation *)
QDot::usage = 
"Generally noncommutative multiplication between quantum objects."
QDot = CenterDot;
SetAttributes[CenterDot, {Flat, OneIdentity}]
(* funny notation: a ~QDot~ b \[Congruent] a \[CircleDot] b *)

(* general arithmetic *)
(* I agonized over the \[Alpha]\[CenterDot]b\[Beta] case for a full weekend ok. any issues arising from your
use of a commutative multiplication instead of \[CenterDot] & without parentheses are not my problem 
\.af\_(\:30c4)_/\.af *)
(* discriminating constants *)
a_?NumericQ ~QDot~ \[Alpha]_ := a \[Alpha]
\[Alpha]_ ~QDot~ a_?NumericQ := a \[Alpha]
(a_?NumericQ \[Alpha]_) ~QDot~ \[Beta]_ := a \[Alpha] ~QDot~ \[Beta]
\[Alpha]_ ~QDot~ (b_?NumericQ \[Beta]_) := b \[Alpha] ~QDot~ \[Beta]
(* powers *)
(\[Alpha]_^(n_:1)) ~QDot~ (\[Alpha]_^(m_:1)) := \[Alpha]^(n+m)

(* compound operator structures *)
\!\(\*OverscriptBox[
SuperscriptBox[\(Q_\), \(n_ : 1\)], \(^\)]\) ~QDot~ \!\(\*OverscriptBox[
SuperscriptBox[\(Q_\), \(m_ : 1\)], \(^\)]\) ^:= \!\(\*OverscriptBox[
SuperscriptBox[\(Q\), \(n + m\)], \(^\)]\)
(*Overscript[O_, ^] ~QDot~ Overscript[Q_, ^] ^:= Overscript[(O ~QDot~ Q), ^]*)

(* bras n kets *)
Bra[{g_}] ~QDot~ Ket[{f_}] ^:= BraKet[{g}, {f}]
(*Ket/: Q_ Ket[{f_}] := Q ~QDot~ Ket[{f}]*)
\!\(\*OverscriptBox[\(Q_\), \(^\)]\) ~QDot~ Ket[{f_}] ^:= Ket[{\!\(\*OverscriptBox[\(Q\), \(^\)]\) ~QDot~ f}]

(* disobedient edge case *)
\[Alpha]_ Ket[{f_}] ^:= \[Alpha] ~QDot~ Ket[{f}] /; !NumericQ[\[Alpha]]


(* Operator Application Product *)
QMult::usage = 
"Generally noncommutative multiplication for applying \
operators to expressions."
QMult = NonCommutativeMultiply;
(*SetAttributes[Application, {Flat, OneIdentity}]*)

(* scalar case *)
\[Alpha]_ ~QMult~ fx_ := \[Alpha] fx /; NumericQ[\[Alpha]] \[Or] !QObjQ[\[Alpha]]
(* evaluation order *)(*
QMult[O_, Q_, fx_] := O ~QMult~ (Q ~QMult~ fx)*)

(* operator applications *)
\!\(\*OverscriptBox[\(\(Q_\)\(\ \)\), \(^\)]\)~QMult~ fx_ ^:= \!\(\*OverscriptBox[\(Q\), \(^\)]\) @ fx
\!\(\*OverscriptBox[
SuperscriptBox[\(Q_\), \(0\)], \(^\)]\) ~QMult~ fx_ ^:= fx
\!\(\*OverscriptBox[
SuperscriptBox[\(Q_\), \(n_\)], \(^\)]\) ~QMult~ fx_ ^:= \!\(\*OverscriptBox[\(Q\), \(^\)]\) ~QMult~ (\!\(\*OverscriptBox[
SuperscriptBox[\(Q\), \(n - 1\)], \(^\)]\) ~QMult~ fx)
(\[Alpha]_ + \[Beta]_) ~QMult~ fx_ ^:= (\[Alpha] ~QMult~ fx) + (\[Beta] ~QMult~ fx)

(* generalized operator structures *)
(a_?NumericQ Q_) ~QMult~ fx_ ^:= a Q ~QMult~ fx
(*(Overscript[Q_, ^] ~QDot~ \[Alpha]_) ~QMult~ fx_ ^:= Overscript[Q, ^] ~QMult~ (\[Alpha] fx)*)
(O_ ~QDot~ Q_) ~QMult~ fx_ ^:= O ~QMult~ (Q ~QMult~ fx)

Bra[{x}] ~QDot~ Ket[{\!\(\*OverscriptBox[\(Q_\), \(^\)]\) ~QDot~ f_}] ^:= \!\(\*OverscriptBox[\(Q\), \(^\)]\) ~QMult~ BraKet[{x}, {f}]
Bra[{x}] ~QDot~ Q_ ~QDot~ Ket[{f_}] ^:= Q ~QMult~ BraKet[{x}, {f}]


(* Commutator *)
Commutator::usage = 
"Commutator[\!\(\*
StyleBox[\"g\",\nFontSlant->\"Italic\"]\), \!\(\*
StyleBox[\"h\",\nFontSlant->\"Italic\"]\)] evaluates the ring element commutator \!\(\*
StyleBox[\"g\",\nFontSlant->\"Italic\"]\)\[CenterDot]\!\(\*
StyleBox[\"h\",\nFontSlant->\"Italic\"]\) - \!\(\*
StyleBox[\"h\",\nFontSlant->\"Italic\"]\)\[CenterDot]\!\(\*
StyleBox[\"g\",\nFontSlant->\"Italic\"]\).
Commutator[\!\(\*
StyleBox[\"g\",\nFontSlant->\"Italic\"]\), \!\(\*
StyleBox[\"h\",\nFontSlant->\"Italic\"]\), \!\(\*
StyleBox[\"fx\",\nFontSlant->\"Italic\"]\)] applies the test function \!\(\*
StyleBox[\"fx\",\nFontSlant->\"Italic\"]\) and divides it out."
Commutator[g_, h_] := (g ~QDot~ h - h ~QDot~ g)
Commutator[g_, h_, fx_] := (Simplify[Commutator[g, h] ~QMult~ fx]) / fx


(* Basis Projection *)(*
BraKet[{x},{x}]=1;
BraKet[{p},{p}]=1;
BraKet[{x},{p}]=E^(I/\[HBar] x p)/\[Sqrt](2\[Pi] \[HBar]);
BraKet[{x},{f_}]:=f[x]
BraKet[{g_},{x}] := Simplify[BraKet[{x},{g}]\[Conjugate]]
*)


(* Inner Product *)
QInner::usage =
"QInner[\!\(\*
StyleBox[\"g\",\nFontSlant->\"Italic\"]\), \!\(\*
StyleBox[\"f\",\nFontSlant->\"Italic\"]\)] \
computes the inner product \
\!\(\*TemplateBox[{StyleBox[\"g\", FontSlant -> \"Italic\"], StyleBox[\"f\", FontSlant -> \"Italic\"]},\n\"BraKet\"]\) in the position basis.
QInner[\!\(\*
StyleBox[\"g\",\nFontSlant->\"Italic\"]\), \!\(\*
StyleBox[\"f\",\nFontSlant->\"Italic\"]\), \!\(\*
StyleBox[\"e\",\nFontSlant->\"Italic\"]\)] \
computes the inner product \
\!\(\*TemplateBox[{StyleBox[\"g\", FontSlant -> \"Italic\"], StyleBox[\"f\", FontSlant -> \"Italic\"]},\n\"BraKet\"]\) in the basis e."
QInner[g_, f_] := QInner[g,f,x]
QInner[g_, f_, e_] := \!\(
\*SubsuperscriptBox[\(\[Integral]\), \(-\[Infinity]\), \(\[Infinity]\)]\(\*
TemplateBox[{"g", "e"},
"BraKet"] \*
TemplateBox[{"e", "f"},
"BraKet"] \[DifferentialD]e\)\)

(*BraKet[{g_}, {f_}] := \!\(
\*SubsuperscriptBox[\(\[Integral]\), \(-\[Infinity]\), \(\[Infinity]\)]\(\*
TemplateBox[{"g", "x"},
"BraKet"]\*
TemplateBox[{"x", "f"},
"BraKet"]\[DifferentialD]x\)\)*)


(* Expectation Value *)
QMean[fx_, f_] := QMean[fx, f, f]
QMean[fx_, g_, f_] := Bra[{g}] ~QDot~ fx ~QDot~ Ket[{f}]


(* Safety On *)
Protect @@ PATIENTS
Clear[PATIENTS]


EndPackage[]
