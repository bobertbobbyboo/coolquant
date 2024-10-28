(* ::Package:: *)

BeginPackage["CoolQuant`"]


(* Constants/Variables *)
VARASSUME = {m\[Element]Reals, m>0, \[Omega]\[Element]Reals, \[Omega]>0, \[HBar]\[Element]Reals, \[HBar]>0, x\[Element]Reals, p\[Element]Reals};
$Assumptions = If[$Assumptions===True, VARASSUME, Join[$Assumptions, VARASSUME]];
SetAttributes[{m, \[Omega], \[HBar]}, Constant]
(* QParamQ/QNumericQ? *)

(* Number Questions *)
(* \[HBar] etc. cannot be genuinely numeric with Mathematica's implementations
while preserving assumptions, so check for constancy instead. *)
(* Check evals the first expression and returns, unless messages are generated
in which case it returns the second. Quiet suppresses the messages. *)
ConstantQ[expr_] := Quiet @ Check[Attributes[expr] ~ContainsAll~ {Constant}, False]
QNumericQ[expr_] := NumericQ[expr] \[Or] ConstantQ[expr] \[Or] BraKetQ[expr]

(* Parameter Conventions:
	a, b etc. scalars
	\[Alpha], \[Beta] etc. general objects
	Bra[{g}], Ket[{f}] bra-ket
	Overscript[O, ^], Overscript[Q, ^] operators
	fx unevaluated expressions
*)


(* Safety Off *)
(* we are performing open-heart surgery on the following operations. *)
(* IMPORTANT: lower definitions overwrite higher definitions given same Tag. *)
(* reprotect at the end!! *)
PATIENTS = {Plus, Times, Power, CenterDot, NonCommutativeMultiply};
Unprotect @@ PATIENTS


(* Quantum Objects (operators, bras, kets) *)
(* _h is anything with the head h, a_. denotes optional pattern *)
(* The -Q (question) functions find generalized objects of a type.
	Base types are associated with heads, e.g. _Ket for kets. *)
OperatorQ[expr_] := MatchQ[Distribute @ expr, a_. _Operator^b_. + \[Beta]_.] \
					\[Or] MatchQ[Distribute @ expr, a_. \[Alpha]_ ~QDot~ Q_?OperatorQ + \[Beta]_.] \
					\[Or] MatchQ[Distribute @ expr, a_. Q_?OperatorQ ~QDot~ \[Alpha]_ + \[Beta]_.]
KetQ[expr_] := MatchQ[expr, a_. _Ket] \[Or] MatchQ[expr, a_. \[Alpha]_ ~QDot~ \[Beta]_?KetQ]
BraQ[expr_] := MatchQ[expr, a_. _Bra] \[Or] MatchQ[expr, a_. \[Beta]_?BraQ ~QDot~ \[Alpha]_]
BraKetQ[expr_] := MatchQ[expr, _BraKet] \[Or] MatchQ[expr, a_?QNumericQ _BraKet]
QObjQ[expr_] := OperatorQ[expr] \[Or] KetQ[expr] \[Or] BraQ[expr]


(* Operators *)
Operator = OverHat;
\!\(\*OverscriptBox[\(x\), \(^\)]\)[fx_] := x fx
\!\(\*OverscriptBox[\(p\), \(^\)]\)[fx_] := -I \[HBar] \!\(
\*SubscriptBox[\(\[PartialD]\), \(x\)]fx\)
(*Overscript[H, ^][fx_] := Overscript[p, ^]*)


(* Bra-ket Notation *)
Ket /: Ket[{f_}]\[ConjugateTranspose] := Bra[{f}]
Bra /: Bra[{f_}]\[ConjugateTranspose] := Ket[{f}]


(* Dot Operation *)
QDot::usage = 
"Generally noncommutative multiplication between quantum objects.";
QDot = CenterDot;
SetAttributes[CenterDot, {Flat, OneIdentity}]
(* funny notation: a ~QDot~ b \[Congruent] a \[CircleDot] b *)

(* general arithmetic *)
(* I agonized over the \[Alpha]\[CenterDot]b\[Beta] case for a full weekend ok. any issues arising from your
use of a commutative multiplication instead of \[CenterDot] & without parentheses are not my problem 
\.af\_(\:30c4)_/\.af *)
(* discriminating constants *)
a_?QNumericQ ~QDot~ \[Alpha]_ := a \[Alpha]
\[Alpha]_ ~QDot~ a_?QNumericQ := a \[Alpha]
(a_?QNumericQ \[Alpha]_) ~QDot~ \[Beta]_ := a \[Alpha] ~QDot~ \[Beta]
\[Alpha]_ ~QDot~ (b_?QNumericQ \[Beta]_) := b \[Alpha] ~QDot~ \[Beta]
(* powers *)
(\[Alpha]_^(n_:1)) ~QDot~ (\[Alpha]_^(m_:1)) := \[Alpha]^(n+m)

(* compound operator structures *)
(*Overscript[(Q_^(n_:1)), ^] ~QDot~ Overscript[(Q_^(m_:1)), ^] ^:= Overscript[Q^(n+m), ^]*)
(*Overscript[O_, ^] ~QDot~ Overscript[Q_, ^] ^:= Overscript[(O ~QDot~ Q), ^]*)
(* translations *)
\!\(\*OverscriptBox[
SuperscriptBox[\(Q_\), \(n_\)], \(^\)]\) ^:= \!\(\*OverscriptBox[\(Q\), \(^\)]\)^n
\!\(\*OverscriptBox[\((O_\ ~QDot~\ Q_)\), \(^\)]\) ^:= \!\(\*OverscriptBox[\(O\), \(^\)]\) \[CenterDot] \!\(\*OverscriptBox[\(Q\), \(^\)]\)

(* bras n kets *)
Bra[{g_}] ~QDot~ Ket[{f_}] ^:= BraKet[{g}, {f}]
\!\(\*OverscriptBox[\(Q_\), \(^\)]\) ~QDot~ Ket[{f_}] ^:= Ket[{\!\(\*OverscriptBox[\(Q\), \(^\)]\) ~QDot~ f}]

(* disobedient usage edge case *)
\[Alpha]_ Ket[{f_}] ^:= \[Alpha] ~QDot~ Ket[{f}] /; !QNumericQ[\[Alpha]]


(* Operator Application Product *)
QMult::usage = 
"Generally noncommutative multiplication for applying \
operators to expressions.";
QMult = NonCommutativeMultiply;
(*SetAttributes[Application, {Flat, OneIdentity}]*)

(* scalar case *)
\[Alpha]_ ~QMult~ fx_ := \[Alpha] fx /; !QObjQ[\[Alpha]]
(* evaluation order *)(*
QMult[O_, Q_, fx_] := O ~QMult~ (Q ~QMult~ fx)*)

(* operator applications *)
\!\(\*OverscriptBox[\(\(Q_\)\(\ \)\), \(^\)]\)~QMult~ fx_ ^:= \!\(\*OverscriptBox[\(Q\), \(^\)]\) @ fx
(*Overscript[(Q_^0), ^] ~QMult~ fx_ ^:= fx*)
(\!\(\*OverscriptBox[\(Q_\), \(^\)]\)^n_) ~QMult~ fx_ ^:= \!\(\*OverscriptBox[\(Q\), \(^\)]\) ~QMult~ ((\!\(\*OverscriptBox[\(Q\), \(^\)]\)^(n-1)) ~QMult~ fx)
(\[Alpha]_ + \[Beta]_) ~QMult~ fx_ ^:= (\[Alpha] ~QMult~ fx) + (\[Beta] ~QMult~ fx)

(* generalized operator structures *)
(a_?QNumericQ Q_) ~QMult~ fx_ ^:= a Q ~QMult~ fx
(O_ ~QDot~ Q_) ~QMult~ fx_ ^:= O ~QMult~ (Q ~QMult~ fx)

(*Bra[{x}] ~QDot~ Ket[{Overscript[Q_, ^] ~QDot~ f_}] ^:= Overscript[Q, ^] ~QMult~ BraKet[{x}, {f}]*)
QDot[Bra[{x}], Q_, Ket[{f_}]] ^:= Q ~QMult~ BraKet[{x}, {f}]


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
StyleBox[\"fx\",\nFontSlant->\"Italic\"]\) and divides it out.";
Commutator[g_, h_] := (g ~QDot~ h - h ~QDot~ g)
Commutator[g_, h_, fx_] := (Simplify[Commutator[g, h] ~QMult~ fx]) / fx


(* Basis Projection *)
QEval::usage = 
"QEval[\!\(\*TemplateBox[{StyleBox[\"g\", FontSlant -> \"Italic\"], StyleBox[\"f\", FontSlant -> \"Italic\"]},\n\"BraKet\"]\)] evaluates the BraKet \!\(\*TemplateBox[{StyleBox[\"g\", FontSlant -> \"Italic\"], StyleBox[\"f\", FontSlant -> \"Italic\"]},\n\"BraKet\"]\).";
(* general *)
QEval[\[Alpha]_] := \[Alpha]
QEval[\[Alpha]_ \[Beta]_] := QEval[\[Alpha]]QEval[\[Beta]]

BraKet[{x}, {x}] = 1;
BraKet[{p}, {p}] = 1;
QEval[BraKet[{x}, {p}]] = E^(I/\[HBar] x p)/\[Sqrt](2\[Pi] \[HBar]);
QEval[BraKet[{x}, {f_}]] := f[x]
QEval[BraKet[{g_}, {x}]] := Simplify[QEval[BraKet[{x}, {g}]]\[Conjugate]]
QEval[BraKet[{g_}, {f_}]] := g ~QInner~ f


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
\!\(\*TemplateBox[{StyleBox[\"g\", FontSlant -> \"Italic\"], StyleBox[\"f\", FontSlant -> \"Italic\"]},\n\"BraKet\"]\) in the basis \!\(\*
StyleBox[\"e\",\nFontSlant->\"Italic\"]\).";
QInner[g_, f_, e_:x] := \!\(
\*SubsuperscriptBox[\(\[Integral]\), \(-\[Infinity]\), \(\[Infinity]\)]\(QEval[\*
TemplateBox[{"g", "e"},
"BraKet"] \*
TemplateBox[{"e", "f"},
"BraKet"]] \[DifferentialD]e\)\)


(* Expectation Value *)
QMean[fx_, f_] := QMean[fx, f, f]
QMean[fx_, g_, f_] := Bra[{g}] ~QDot~ fx ~QDot~ Ket[{f}]


(* Safety On *)
Protect @@ PATIENTS
Clear[PATIENTS]


EndPackage[]
