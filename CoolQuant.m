(* ::Package:: *)

BeginPackage["CoolQuant`"];


(* Assumptions *)
(* add one or a list of assumptions *)
AddGlobalAssumption[expr_] :=
	$Assumptions = Assuming[expr, $Assumptions]


(* Constants/Variables *)
(* square well width, mass, frequency, Planck constant, speed of light *)
CONSTS = {l, m, \[Omega], \[HBar], c0};
(* add assumptions *)
AddGlobalAssumption @ Positive[CONSTS];
(* make constants constant and protected.
	use rules to adjust values. *)
Evaluate @ CONSTS ~SetAttributes~ Constant
Protect @@ CONSTS;
ClearAll[CONSTS, VARASSUME]

(* Number Questions *)
(* \[HBar] etc. cannot be genuinely numeric with Mathematica's implementations
while preserving assumptions, so check for constancy instead. *)
(* Check evals the first expression and returns, unless messages are generated,
in which case it returns the second. Quiet suppresses the messages. *)
ConstantQ[expr_] := Quiet @ Check[Attributes[expr] ~ContainsAll~ {Constant}, False]
(* scalar-like *)
(* use QNumeric for symbols/values, QBased for expressions *)
QNumericQ[expr_] := NumericQ[expr] \[Or] ConstantQ[expr]

(* Parameter Conventions:
	a, b etc. scalars
	\[Alpha], \[Beta] etc. general objects
	\[Xi] x-like, \[Pi] p-like
	Bra[{g}], Ket[{f}] bra-ket
	Overscript[O, ^], Overscript[Q, ^] operators
	fx unevaluated expressions
*)
(* turn off the annoying shadow message *)
(*Off[General::shdw]*)
(*Off @@ {x::shdw, p::shdw}*)


(* Compatible Bases *)
StdBases = Sequence[x, p];
AddGlobalAssumption @ (e_?(QBasis[x, p])\[Element]Reals)

(* get a function that returns whether input is e-like *)
QBasis[e_][expr_] :=
	MatchQ[expr, e] \[Or] MatchQ[expr, Subscript[e, n_]] \
	\[Or] MatchQ[expr, Derivative[1][e]] \[Or] MatchQ[expr, Derivative[1][Subscript[e, n_]]]
(* e1 or e2 or... *)
(* use an outer product where the multiplication is applying a map *)
QBasis[e__][expr_] := Or @@ Flatten @ Outer[#1 @ #2 &, QBasis /@ {e}, {expr}]
(* very based. could be a derivative, idfk anymore *)
(* QUnbased \[DoubleLeftRightArrow] QDot always commutes *)
(* QNumeric \[Implies] QUnbased *)
QBased[\[Alpha]_?BraKetQ]
(* derivative wrt \[Xi] is zero *)
Independent[]


(* Quantum Objects (operators, bras, kets) *)
(* _h is anything with the head h, a_. denotes optional pattern *)
(* the -Q (question) functions find generalized objects of a type.
	base types are associated with heads, e.g. _Ket for kets. *)
OperatorQ[expr_] :=
	MatchQ[Expand @ expr, a_. _Operator^b_. + \[Beta]_.] \
	\[Or] MatchQ[Expand @ expr, a_. \[Alpha]_ ~QDot~ Q_?OperatorQ + \[Beta]_.] \
	\[Or] MatchQ[Expand @ expr, a_. Q_?OperatorQ ~QDot~ \[Alpha]_ + \[Beta]_.]
(* linear combinations of kets are kets, same with bras *)
KetQ[expr_] :=
	MatchQ[expr, a_. _Ket] \
	\[Or] MatchQ[expr, a_. \[Alpha]_ ~QDot~ \[Beta]_?KetQ] \
	\[Or] MatchQ[expr, \[Alpha]_?KetQ + \[Beta]_?KetQ]
BraQ[expr_] :=
	MatchQ[expr, a_. _Bra] \
	\[Or] MatchQ[expr, a_. \[Beta]_?BraQ ~QDot~ \[Alpha]_] \
	\[Or] MatchQ[expr, \[Alpha]_?BraQ + \[Beta]_?BraQ]
QVectorQ[expr_]
BraKetQ[expr_] := 
	!FreeQ[expr, _BraKet]
QObjQ[expr_] := OperatorQ[expr] \[Or] KetQ[expr] \[Or] BraQ[expr]
(* whether head indicates base Q object *)
QHeadQ[expr_] := {Operator, Ket, Bra} ~AnyTrue~ SameAs[Head @ expr]


(* Operators *)
Operator = OverHat;
\!\(\*OverscriptBox[\(\[Xi]_?\((QBasis[x])\)\), \(^\)]\)[fx_] := \[Xi] fx
\!\(\*OverscriptBox[\(p\), \(^\)]\)[fx_] := -I \[HBar] \!\(
\*SubscriptBox[\(\[PartialD]\), \(x\)]fx\)
(* derivative *)
\!\(\*OverscriptBox[\(D\), \(^\)]\)[fx_] := \!\(
\*SubscriptBox[\(\[PartialD]\), \(x\)]fx\)


(* Safety Off *)
(* we are performing open-heart surgery on the following operations. *)
(* IMPORTANT: lower definitions overwrite higher definitions given same Tag. 
	define function properties (e.g. distributivity, associativity) before
	specific object cases! *)
(* reprotect at the end!! *)
PATIENTS = {Plus, Times, Power, CenterDot, NonCommutativeMultiply};
Unprotect @@ PATIENTS;


(* Bra-ket Notation *)
(* Hermitian Conjugation *)
Ket /: Ket[{f_}]\[ConjugateTranspose] := Bra[{f}]
Bra /: Bra[{f_}]\[ConjugateTranspose] := Ket[{f}]

HermitianQ
QConj


(* Dot Operation *)
(* noncommutative multiplication *)
(* commutativity is governed by the attribute Orderless *)
QDot::usage = 
"\!\(\*
	StyleBox[\"\[Alpha]\", \"TR\"]
\) \[CenterDot] \!\(\*
	StyleBox[\"\[Beta]\", \"TR\"]
\) \[CenterDot] \!\(\*
	StyleBox[\"\[Gamma]\", \"TR\"]
\) represents a generally noncommutative product of quantum objects.";
QDot = CenterDot;
Off @ QDot::shdw
SetAttributes[CenterDot, {Flat, OneIdentity}]
(* funny notation: a ~QDot~ b \[Congruent] a \[CircleDot] b *)

(* general arithmetic *)
(* I agonized over the \[Alpha]\[CenterDot]b\[Beta] case for a full weekend ok. any issues arising from use of
	commutative multiplication instead of \[CenterDot] & without parentheses are not my problem 
	\.af\_(\:30c4)_/\.af *)
(* L/R distributivity over + *)
\[Alpha]_ ~QDot~ (\[Beta]_ + \[Gamma]_) := \[Alpha] ~QDot~ \[Beta] + \[Alpha] ~QDot~ \[Gamma]
(\[Alpha]_ + \[Beta]_) ~QDot~ \[Gamma]_ := \[Alpha] ~QDot~ \[Gamma] + \[Beta] ~QDot~ \[Gamma]
(* powers *)
(\[Alpha]_^(n_:1)) ~QDot~ (\[Alpha]_^(m_:1)) := \[Alpha]^(n+m)

(* commutativity/homogeneity for QNumerics *)
a_?QNumericQ ~QDot~ \[Alpha]_ := a \[Alpha]
\[Alpha]_ ~QDot~ a_?QNumericQ := a \[Alpha]
(a_?QNumericQ \[Alpha]_) ~QDot~ \[Beta]_ := a \[Alpha] ~QDot~ \[Beta]
\[Alpha]_ ~QDot~ (b_?QNumericQ \[Beta]_) := b \[Alpha] ~QDot~ \[Beta]

(* compound operator structures *)
(*Overscript[(Q_^(n_:1)), ^] ~QDot~ Overscript[(Q_^(m_:1)), ^] ^:= Overscript[Q^(n+m), ^]*)
(*Overscript[O_, ^] ~QDot~ Overscript[Q_, ^] ^:= Overscript[(O ~QDot~ Q), ^]*)
(* translations *)
\!\(\*OverscriptBox[
SuperscriptBox[\(Q_\), \(n_\)], \(^\)]\) ^:= \!\(\*OverscriptBox[\(Q\), \(^\)]\)^n
\!\(\*OverscriptBox[\((O_\  + \ Q_)\), \(^\)]\) ^:= \!\(\*OverscriptBox[\(O\), \(^\)]\) + \!\(\*OverscriptBox[\(Q\), \(^\)]\)
\!\(\*OverscriptBox[\((O_\ ~QDot~\ Q_)\), \(^\)]\) ^:= \!\(\*OverscriptBox[\(O\), \(^\)]\) ~QDot~ \!\(\*OverscriptBox[\(Q\), \(^\)]\)

(* bras n kets *)
Bra[{g_}] ~QDot~ Ket[{f_}] ^:= BraKet[{g}, {f}]
\!\(\*OverscriptBox[\(Q_\), \(^\)]\) ~QDot~ Ket[{f_}] ^:= Ket[{\!\(\*OverscriptBox[\(Q\), \(^\)]\) ~QDot~ f}]
(* on function projected into basis *)
(* delay operator evaluation until QEval *)
QDot[Bra[{e_?(QBasis[x, p])}], Q_, Ket[{f_}]] := Q ~QDot~ BraKet[{e}, {f}]
BraKet[{e_?(QBasis[x, p])}, {Q_ ~QDot~ f_}] := Q ~QDot~ BraKet[{e}, {f}]

(* disobedient \[Times] usage edge case *)
\[Alpha]_ Ket[{f_}] ^:= \[Alpha] ~QDot~ Ket[{f}] /; !QNumericQ[\[Alpha]]


(* Operator Application Product *)
QMult::usage = 
"Generally noncommutative application product.
For an operator \!\(\*
	StyleBox[
		OverscriptBox[\"Q\", \"^\"],
		\"TI\"
	]
\), \!\(\*
	StyleBox[
		OverscriptBox[\"Q\", \"^\"],
		\"TI\"
	]
\) ** \!\(\*
	StyleBox[\"fx\", \"TI\"]
\) applies \!\(\*
	StyleBox[
		OverscriptBox[\"Q\", \"^\"], 
		\"TI\"
	]
\) to the expression \!\(\*
	StyleBox[\"fx\", \"TI\"]
\) as \!\(\*
	StyleBox[
		OverscriptBox[\"Q\", \"^\"], 
		\"TI\"
	]
\)[\!\(\*
	StyleBox[\"fx\", \"TI\"]
\)].
For a nonoperator quantum object \!\(\*
	StyleBox[\"\[Alpha]\", \"TR\"]
\), \!\(\*
	StyleBox[\"\[Alpha]\", \"TR\"]
\) ** \!\(\*
	StyleBox[\"fx\", \"TI\"]
\) becomes \!\(\*
	StyleBox[\"\[Alpha]\", \"TR\"]
\) \[CenterDot] \!\(\*
	StyleBox[\"fx\", \"TI\"]
\).
Otherwise, the operation defaults to usual multiplication."
QMult = NonCommutativeMultiply;
(*SetAttributes[Application, {Flat, OneIdentity}]*)

(* evaluation order *)(*
QMult[O_, Q_, fx_] := O ~QMult~ (Q ~QMult~ fx)*)

(* generalized operator structures *)
(* R distributivity over + *)
(O_ + Q_) ~QMult~ fx_ := (O ~QMult~ fx) + (Q ~QMult~ fx)
(* \[Times] compatibility *)
(a_ Q_) ~QMult~ fx_ := a Q ~QMult~ fx
(* QDot compatibility *)
(O_ ~QDot~ Q_) ~QMult~ fx_ := O ~QMult~ (Q ~QMult~ fx)

(* nonoperator cases *)
\[Alpha]_ ~QMult~ fx_ := \[Alpha] QEval @ fx /; !QObjQ[\[Alpha]]
\[Alpha]_?QObjQ ~QMult~ fx_ := \[Alpha] \[CenterDot] fx /; !OperatorQ[\[Alpha]]

(* base operator applications *)
\!\(\*OverscriptBox[\(\(Q_\)\(\ \)\), \(^\)]\)~QMult~ fx_ ^:= \!\(\*OverscriptBox[\(Q\), \(^\)]\) @ QEval @ fx
(\!\(\*OverscriptBox[\(Q_\), \(^\)]\)^n_) ~QMult~ fx_ ^:= \!\(\*OverscriptBox[\(Q\), \(^\)]\) ~QMult~ ((\!\(\*OverscriptBox[\(Q\), \(^\)]\)^(n-1)) ~QMult~ fx)

(* function composition *)
(*(f_ ~QDot~ g_)[args__] := f ~QMult~ g @ args*)


(* Commutator *)
Commutator::usage = 
"Commutator[\!\(\*
	StyleBox[\"g\", \"TI\"]
\), \!\(\*
	StyleBox[\"h\", \"TI\"]
\)] evaluates the ring element commutator \!\(\*
	StyleBox[\"g\", \"TI\"]
\) \[CenterDot] \!\(\*
	StyleBox[\"h\", \"TI\"]
\) - \!\(\*
	StyleBox[\"h\", \"TI\"]
\) \[CenterDot] \!\(\*
	StyleBox[\"g\", \"TI\"]
\).
Commutator[\!\(\*
	StyleBox[\"g\", \"TI\"]
\), \!\(\*
	StyleBox[\"h\", \"TI\"]
\), \!\(\*
	StyleBox[\"fx\", \"TI\"]
\)] applies the test expression \!\(\*
	StyleBox[\"fx\", \"TI\"]
\) and divides it out.";
Commutator[g_, h_] := (g ~QDot~ h - h ~QDot~ g)
Commutator[g_, h_, fx_] := Commutator[g, h] ~QMult~ fx / fx //Simplify

QTest (* apply f[x] and divide out *)


(* Bra-Ket (and Operator Structure) Evaluation *)
QEval::usage = 
"QEval[\!\(\*
	TemplateBox[
		{
			StyleBox[\"g\", \"TI\"], 
			StyleBox[\"f\", \"TI\"]
		},
		\"BraKet\"
	]
\)] evaluates the bra-ket \!\(\*
	TemplateBox[
		{
			StyleBox[\"g\", \"TI\"], 
			StyleBox[\"f\", \"TI\"]
		},
		\"BraKet\"
	]
\).
QEval[\!\(\*
	StyleBox[\"f\", \"TI\"]
\)[\!\(\*
	SubscriptBox[
		StyleBox[\"expr\", \"TI\"], 
		\(1\)
	]
\), \!\(\*
	SubscriptBox[
		StyleBox[\"expr\", \"TI\"], 
		\(2\)
	]
\), ...]] evaluates each inner expression recursively, i.e. \!\(\*
	StyleBox[\"f\", \"TI\"]
\)[QEval[\!\(\*
	SubscriptBox[
		StyleBox[\"expr\", \"TI\"], 
		\(1\)
	]
\)], QEval[\!\(\*
	SubscriptBox[
		StyleBox[\"expr\", \"TI\"], 
		\(2\)
	]
\)], ...].";
(* general values *)
QEval @ \[Alpha]_ := \[Alpha]
(* direct operator structure evaluation *)
(* QDot -> QMult *)
QEval @ Q_?OperatorQ := Q ~QMult~ 1

(* Dirac delta functions *)
QEval @ BraKet[{\[Xi]1_?(QBasis[x])}, {\[Xi]2_?(QBasis[x])}] := DiracDelta[\[Xi]1 - \[Xi]2];
QEval @ BraKet[{\[Mu]1_?(QBasis[p])}, {\[Mu]2_?(QBasis[p])}] := DiracDelta[\[Mu]1 - \[Mu]2];
(* projections *)
QEval @ BraKet[{\[Xi]_?(QBasis[x])}, {\[Mu]_?(QBasis[p])}] := E^(I/\[HBar] \[Xi] \[Mu])/\[Sqrt](2\[Pi] \[HBar]);
QEval @ BraKet[{g_}, {e_?(QBasis[x, p])}] := Simplify[QEval @ BraKet[{e}, {g}]\[Conjugate]]
QEval @ BraKet[{\[Xi]_?(QBasis[x])}, {f_}] := f[\[Xi]]
QEval @ BraKet[{\[Mu]_?(QBasis[p])}, {f_}] := \!\(\*OverscriptBox[\(f\), \(~\)]\)[\[Mu]]
QEval @ BraKet[{g_}, {f_}] := g ~QInner~ f

(* recursive application *)
QEval @ f_[args__] := f @@ QEval /@ {args} /; !QHeadQ[f[args]]


(* Inner Product *)
QInner::usage =
"QInner[\!\(\*
	StyleBox[\"g\", \"TI\"]
\), \!\(\*
	StyleBox[\"f\", \"TI\"]
\)] computes the inner product \!\(\*
	TemplateBox[
		{
			StyleBox[\"g\", \"TI\"],
			StyleBox[\"f\", \"TI\"]
		}, 
		\"BraKet\"
	]
\) in the position basis.
QInner[\!\(\*
	StyleBox[\"g\", \"TI\"]
\), \!\(\*
	StyleBox[\"f\", \"TI\"]
\), \!\(\*
	StyleBox[\"e\", \"TI\"]
\)] computes the inner product \!\(\*
	TemplateBox[
		{
			StyleBox[\"g\", \"TI\"],
			StyleBox[\"f\", \"TI\"]
		},
		\"BraKet\"
	]
\) with respect to the basis element \!\(\*
	StyleBox[\"\!\(\*SuperscriptBox[\(e\), \(\[Prime]\)]\)\", \"TI\"]
\).";
(* confusion? check for missing primes *)
QInner[g_, f_, e_:x] := \!\(
\*SubsuperscriptBox[\(\[Integral]\), \(-\[Infinity]\), \(\[Infinity]\)]\(QEval[\*
TemplateBox[{"g", SuperscriptBox["e", "\[Prime]"]},
"BraKet"] \*
TemplateBox[{SuperscriptBox["e", "\[Prime]"], "f"},
"BraKet"]] \[DifferentialD]
\*SuperscriptBox[\(e\), \(\[Prime]\)]\)\)


(* Expectation Value *)
(* lazy by default, use QEval for numeric *)
QMean[fx_, f_] := QMean[fx, f, f]
QMean[fx_, g_, f_] := Bra[{g}] ~QDot~ fx ~QDot~ Ket[{f}]


(* Fourier Transform *)
QFourier


(* Safety On *)
Protect @@ PATIENTS;
ClearAll[PATIENTS]


EndPackage[]
