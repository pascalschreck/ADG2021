Load "preamble3D.v".


(* dans constructLemma(), requis par LPQPpOo *)
(* dans la couche 0 *)
Lemma LPQRPpOo : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Oo ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpOo requis par la preuve de (?)PQRPpOo pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpOo requis par la preuve de (?)PQRPpOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpOom2 : rk(P :: Q :: R :: Pp :: Oo :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Oo :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpOom4 : rk(P :: Q :: R :: Pp :: Oo :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Oo :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

assert(HPQRPpOoM : rk(P :: Q :: R :: Pp :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRPpOom : rk(P :: Q :: R :: Pp :: Oo ::  nil) >= 1) by (solve_hyps_min HPQRPpOoeq HPQRPpOom1).
intuition.
Qed.

(* dans constructLemma(), requis par LPQPpOo *)
(* dans la couche 0 *)
Lemma LPQPpOo : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Q :: Pp :: Oo ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PRPpOo requis par la preuve de (?)PQPpOo pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour PRPpOo requis par la preuve de (?)PRPpOo pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpOo requis par la preuve de (?)PRPpOo pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HPRPpOoM3 : rk(P :: R :: Pp :: Oo :: nil) <= 3).
{
	assert(HRMtmp : rk(R :: nil) <= 1) by (solve_hyps_max HReq HRM1).
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (R :: nil) (P :: Pp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: Oo :: nil) (R :: P :: Pp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (R :: P :: Pp :: Oo :: nil) ((R :: nil) ++ (P :: Pp :: Oo :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (R :: nil) (P :: Pp :: Oo :: nil) (nil) 1 2 0 HRMtmp HPPpOoMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPRPpOom2 : rk(P :: R :: Pp :: Oo :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Oo :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PQPpOo requis par la preuve de (?)PQPpOo pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour PQPpOo requis par la preuve de (?)PQPpOo pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQPpOo requis par la preuve de (?)PQPpOo pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HPQPpOoM3 : rk(P :: Q :: Pp :: Oo :: nil) <= 3).
{
	assert(HQMtmp : rk(Q :: nil) <= 1) by (solve_hyps_max HQeq HQM1).
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Q :: nil) (P :: Pp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: Pp :: Oo :: nil) (Q :: P :: Pp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: P :: Pp :: Oo :: nil) ((Q :: nil) ++ (P :: Pp :: Oo :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Q :: nil) (P :: Pp :: Oo :: nil) (nil) 1 2 0 HQMtmp HPPpOoMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQPpOom2 : rk(P :: Q :: Pp :: Oo :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: Pp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: Pp :: Oo :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -4 et 5*)
assert(HPQPpOom3 : rk(P :: Q :: Pp :: Oo :: nil) >= 3).
{
	assert(HPRPpOoMtmp : rk(P :: R :: Pp :: Oo :: nil) <= 3) by (solve_hyps_max HPRPpOoeq HPRPpOoM3).
	assert(HPQRPpOoeq : rk(P :: Q :: R :: Pp :: Oo :: nil) = 4) by (apply LPQRPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQRPpOomtmp : rk(P :: Q :: R :: Pp :: Oo :: nil) >= 4) by (solve_hyps_min HPQRPpOoeq HPQRPpOom4).
	assert(HPPpOomtmp : rk(P :: Pp :: Oo :: nil) >= 2) by (solve_hyps_min HPPpOoeq HPPpOom2).
	assert(Hincl : incl (P :: Pp :: Oo :: nil) (list_inter (P :: Q :: Pp :: Oo :: nil) (P :: R :: Pp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Oo :: nil) (P :: Q :: Pp :: Oo :: P :: R :: Pp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: Pp :: Oo :: P :: R :: Pp :: Oo :: nil) ((P :: Q :: Pp :: Oo :: nil) ++ (P :: R :: Pp :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpOomtmp;try rewrite HT2 in HPQRPpOomtmp.
	assert(HT := rule_2 (P :: Q :: Pp :: Oo :: nil) (P :: R :: Pp :: Oo :: nil) (P :: Pp :: Oo :: nil) 4 2 3 HPQRPpOomtmp HPPpOomtmp HPRPpOoMtmp Hincl);apply HT.
}

assert(HPQPpOoM : rk(P :: Q :: Pp :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQPpOom : rk(P :: Q :: Pp :: Oo ::  nil) >= 1) by (solve_hyps_min HPQPpOoeq HPQPpOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPRPpOo : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: R :: Pp :: Oo ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PRPpOo requis par la preuve de (?)PRPpOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour PRPpOo requis par la preuve de (?)PRPpOo pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpOo requis par la preuve de (?)PRPpOo pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HPRPpOoM3 : rk(P :: R :: Pp :: Oo :: nil) <= 3).
{
	assert(HRMtmp : rk(R :: nil) <= 1) by (solve_hyps_max HReq HRM1).
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (R :: nil) (P :: Pp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: Oo :: nil) (R :: P :: Pp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (R :: P :: Pp :: Oo :: nil) ((R :: nil) ++ (P :: Pp :: Oo :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (R :: nil) (P :: Pp :: Oo :: nil) (nil) 1 2 0 HRMtmp HPPpOoMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPRPpOom2 : rk(P :: R :: Pp :: Oo :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Oo :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 -4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Oo ::  de rang :  4 et 4 	 AiB : P :: Pp :: Oo ::  de rang :  2 et 2 	 A : P :: Q :: Pp :: Oo ::   de rang : 3 et 3 *)
assert(HPRPpOom3 : rk(P :: R :: Pp :: Oo :: nil) >= 3).
{
	assert(HPQPpOoeq : rk(P :: Q :: Pp :: Oo :: nil) = 3) by (apply LPQPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQPpOoMtmp : rk(P :: Q :: Pp :: Oo :: nil) <= 3) by (solve_hyps_max HPQPpOoeq HPQPpOoM3).
	assert(HPQRPpOoeq : rk(P :: Q :: R :: Pp :: Oo :: nil) = 4) by (apply LPQRPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQRPpOomtmp : rk(P :: Q :: R :: Pp :: Oo :: nil) >= 4) by (solve_hyps_min HPQRPpOoeq HPQRPpOom4).
	assert(HPPpOomtmp : rk(P :: Pp :: Oo :: nil) >= 2) by (solve_hyps_min HPPpOoeq HPPpOom2).
	assert(Hincl : incl (P :: Pp :: Oo :: nil) (list_inter (P :: Q :: Pp :: Oo :: nil) (P :: R :: Pp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Oo :: nil) (P :: Q :: Pp :: Oo :: P :: R :: Pp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: Pp :: Oo :: P :: R :: Pp :: Oo :: nil) ((P :: Q :: Pp :: Oo :: nil) ++ (P :: R :: Pp :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpOomtmp;try rewrite HT2 in HPQRPpOomtmp.
	assert(HT := rule_4 (P :: Q :: Pp :: Oo :: nil) (P :: R :: Pp :: Oo :: nil) (P :: Pp :: Oo :: nil) 4 2 3 HPQRPpOomtmp HPPpOomtmp HPQPpOoMtmp Hincl); apply HT.
}

assert(HPRPpOoM : rk(P :: R :: Pp :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPRPpOom : rk(P :: R :: Pp :: Oo ::  nil) >= 1) by (solve_hyps_min HPRPpOoeq HPRPpOom1).
intuition.
Qed.

(* dans constructLemma(), requis par LPRPpRpOo *)
(* dans la couche 0 *)
Lemma LPQRPpRpOo : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Rp :: Oo ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpRpOo requis par la preuve de (?)PQRPpRpOo pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpRp requis par la preuve de (?)PQRPpRpOo pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpRp requis par la preuve de (?)PQRPpRp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpRp requis par la preuve de (?)PQRPpRp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpRpm2 : rk(P :: Q :: R :: Pp :: Rp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Rp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Rp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: -4 -1 et -2*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Rp ::  de rang :  4 et 4 	 AiB :  de rang :  0 et 0 	 A : Qp ::   de rang : 1 et 1 *)
assert(HPQRPpRpm3 : rk(P :: Q :: R :: Pp :: Rp :: nil) >= 3).
{
	assert(HQpMtmp : rk(Qp :: nil) <= 1) by (solve_hyps_max HQpeq HQpM1).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Qp :: nil) (P :: Q :: R :: Pp :: Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (Qp :: P :: Q :: R :: Pp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Qp :: P :: Q :: R :: Pp :: Rp :: nil) ((Qp :: nil) ++ (P :: Q :: R :: Pp :: Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_4 (Qp :: nil) (P :: Q :: R :: Pp :: Rp :: nil) (nil) 4 0 1 HPQRPpQpRpmtmp Hmtmp HQpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpRpOo requis par la preuve de (?)PQRPpRpOo pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpRpOo requis par la preuve de (?)PQRPpRpOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpRpOom2 : rk(P :: Q :: R :: Pp :: Rp :: Oo :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Rp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Rp :: Oo :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPQRPpRpOom3 : rk(P :: Q :: R :: Pp :: Rp :: Oo :: nil) >= 3).
{
	assert(HPQRPpRpmtmp : rk(P :: Q :: R :: Pp :: Rp :: nil) >= 3) by (solve_hyps_min HPQRPpRpeq HPQRPpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Pp :: Rp :: nil) (P :: Q :: R :: Pp :: Rp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Pp :: Rp :: nil) (P :: Q :: R :: Pp :: Rp :: Oo :: nil) 3 3 HPQRPpRpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpRpOom4 : rk(P :: Q :: R :: Pp :: Rp :: Oo :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Rp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Rp :: Oo :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

assert(HPQRPpRpOoM : rk(P :: Q :: R :: Pp :: Rp :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRPpRpOom : rk(P :: Q :: R :: Pp :: Rp :: Oo ::  nil) >= 1) by (solve_hyps_min HPQRPpRpOoeq HPQRPpRpOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPRPpRpOo : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: R :: Pp :: Rp :: Oo ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PRPpRpOo requis par la preuve de (?)PRPpRpOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpRpOo requis par la preuve de (?)PRPpRpOo pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpRpOo requis par la preuve de (?)PRPpRpOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPRPpRpOom2 : rk(P :: R :: Pp :: Rp :: Oo :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Rp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Rp :: Oo :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -2*)
assert(HPRPpRpOoM3 : rk(P :: R :: Pp :: Rp :: Oo :: nil) <= 3).
{
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	assert(HRRpOoMtmp : rk(R :: Rp :: Oo :: nil) <= 2) by (solve_hyps_max HRRpOoeq HRRpOoM2).
	assert(HOomtmp : rk(Oo :: nil) >= 1) by (solve_hyps_min HOoeq HOom1).
	assert(Hincl : incl (Oo :: nil) (list_inter (P :: Pp :: Oo :: nil) (R :: Rp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: Rp :: Oo :: nil) (P :: Pp :: Oo :: R :: Rp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Oo :: R :: Rp :: Oo :: nil) ((P :: Pp :: Oo :: nil) ++ (R :: Rp :: Oo :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P :: Pp :: Oo :: nil) (R :: Rp :: Oo :: nil) (Oo :: nil) 2 2 1 HPPpOoMtmp HRRpOoMtmp HOomtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 -4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Rp :: Oo ::  de rang :  4 et 4 	 AiB : P :: Pp :: Oo ::  de rang :  2 et 2 	 A : P :: Q :: Pp :: Oo ::   de rang : 3 et 3 *)
assert(HPRPpRpOom3 : rk(P :: R :: Pp :: Rp :: Oo :: nil) >= 3).
{
	assert(HPQPpOoeq : rk(P :: Q :: Pp :: Oo :: nil) = 3) by (apply LPQPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQPpOoMtmp : rk(P :: Q :: Pp :: Oo :: nil) <= 3) by (solve_hyps_max HPQPpOoeq HPQPpOoM3).
	assert(HPQRPpRpOoeq : rk(P :: Q :: R :: Pp :: Rp :: Oo :: nil) = 4) by (apply LPQRPpRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQRPpRpOomtmp : rk(P :: Q :: R :: Pp :: Rp :: Oo :: nil) >= 4) by (solve_hyps_min HPQRPpRpOoeq HPQRPpRpOom4).
	assert(HPPpOomtmp : rk(P :: Pp :: Oo :: nil) >= 2) by (solve_hyps_min HPPpOoeq HPPpOom2).
	assert(Hincl : incl (P :: Pp :: Oo :: nil) (list_inter (P :: Q :: Pp :: Oo :: nil) (P :: R :: Pp :: Rp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Rp :: Oo :: nil) (P :: Q :: Pp :: Oo :: P :: R :: Pp :: Rp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: Pp :: Oo :: P :: R :: Pp :: Rp :: Oo :: nil) ((P :: Q :: Pp :: Oo :: nil) ++ (P :: R :: Pp :: Rp :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpRpOomtmp;try rewrite HT2 in HPQRPpRpOomtmp.
	assert(HT := rule_4 (P :: Q :: Pp :: Oo :: nil) (P :: R :: Pp :: Rp :: Oo :: nil) (P :: Pp :: Oo :: nil) 4 2 3 HPQRPpRpOomtmp HPPpOomtmp HPQPpOoMtmp Hincl); apply HT.
}

assert(HPRPpRpOoM : rk(P :: R :: Pp :: Rp :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPRPpRpOom : rk(P :: R :: Pp :: Rp :: Oo ::  nil) >= 1) by (solve_hyps_min HPRPpRpOoeq HPRPpRpOom1).
intuition.
Qed.

(* dans constructLemma(), requis par LPpalpha *)
(* dans constructLemma(), requis par LPRPpalpha *)
(* dans la couche 0 *)
Lemma LPQRPpOoalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Oo :: alpha ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpOoalpha requis par la preuve de (?)PQRPpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpOoalpha requis par la preuve de (?)PQRPpOoalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpOoalpham2 : rk(P :: Q :: R :: Pp :: Oo :: alpha :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Oo :: alpha :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpOoalpham4 : rk(P :: Q :: R :: Pp :: Oo :: alpha :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Oo :: alpha :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

assert(HPQRPpOoalphaM : rk(P :: Q :: R :: Pp :: Oo :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRPpOoalpham : rk(P :: Q :: R :: Pp :: Oo :: alpha ::  nil) >= 1) by (solve_hyps_min HPQRPpOoalphaeq HPQRPpOoalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPRPpalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: R :: Pp :: alpha ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PRPpalpha requis par la preuve de (?)PRPpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour PRPpalpha requis par la preuve de (?)PRPpalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpalpha requis par la preuve de (?)PRPpalpha pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HPRPpalphaM3 : rk(P :: R :: Pp :: alpha :: nil) <= 3).
{
	assert(HPpMtmp : rk(Pp :: nil) <= 1) by (solve_hyps_max HPpeq HPpM1).
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Pp :: nil) (P :: R :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: alpha :: nil) (Pp :: P :: R :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: P :: R :: alpha :: nil) ((Pp :: nil) ++ (P :: R :: alpha :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Pp :: nil) (P :: R :: alpha :: nil) (nil) 1 2 0 HPpMtmp HPRalphaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPRPpalpham2 : rk(P :: R :: Pp :: alpha :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: alpha :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 -4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Oo :: alpha ::  de rang :  4 et 4 	 AiB : P :: Pp ::  de rang :  2 et 2 	 A : P :: Q :: Pp :: Oo ::   de rang : 3 et 3 *)
assert(HPRPpalpham3 : rk(P :: R :: Pp :: alpha :: nil) >= 3).
{
	assert(HPQPpOoeq : rk(P :: Q :: Pp :: Oo :: nil) = 3) by (apply LPQPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQPpOoMtmp : rk(P :: Q :: Pp :: Oo :: nil) <= 3) by (solve_hyps_max HPQPpOoeq HPQPpOoM3).
	assert(HPQRPpOoalphaeq : rk(P :: Q :: R :: Pp :: Oo :: alpha :: nil) = 4) by (apply LPQRPpOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQRPpOoalphamtmp : rk(P :: Q :: R :: Pp :: Oo :: alpha :: nil) >= 4) by (solve_hyps_min HPQRPpOoalphaeq HPQRPpOoalpham4).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hincl : incl (P :: Pp :: nil) (list_inter (P :: Q :: Pp :: Oo :: nil) (P :: R :: Pp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Oo :: alpha :: nil) (P :: Q :: Pp :: Oo :: P :: R :: Pp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: Pp :: Oo :: P :: R :: Pp :: alpha :: nil) ((P :: Q :: Pp :: Oo :: nil) ++ (P :: R :: Pp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpOoalphamtmp;try rewrite HT2 in HPQRPpOoalphamtmp.
	assert(HT := rule_4 (P :: Q :: Pp :: Oo :: nil) (P :: R :: Pp :: alpha :: nil) (P :: Pp :: nil) 4 2 3 HPQRPpOoalphamtmp HPPpmtmp HPQPpOoMtmp Hincl); apply HT.
}

assert(HPRPpalphaM : rk(P :: R :: Pp :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPRPpalpham : rk(P :: R :: Pp :: alpha ::  nil) >= 1) by (solve_hyps_min HPRPpalphaeq HPRPpalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPpalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(Pp :: alpha ::  nil) = 2.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour Ppalpha requis par la preuve de (?)Ppalpha pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 2) *)
(* marque des antécédents AUB AiB A: 4 -2 et -4*)
(* ensembles concernés AUB : P :: R :: Pp :: alpha ::  de rang :  3 et 3 	 AiB : alpha ::  de rang :  1 et 1 	 A : P :: R :: alpha ::   de rang : 2 et 2 *)
assert(HPpalpham2 : rk(Pp :: alpha :: nil) >= 2).
{
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	assert(HPRPpalphaeq : rk(P :: R :: Pp :: alpha :: nil) = 3) by (apply LPRPpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPRPpalphamtmp : rk(P :: R :: Pp :: alpha :: nil) >= 3) by (solve_hyps_min HPRPpalphaeq HPRPpalpham3).
	assert(Halphamtmp : rk(alpha :: nil) >= 1) by (solve_hyps_min Halphaeq Halpham1).
	assert(Hincl : incl (alpha :: nil) (list_inter (P :: R :: alpha :: nil) (Pp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: alpha :: nil) (P :: R :: alpha :: Pp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: alpha :: Pp :: alpha :: nil) ((P :: R :: alpha :: nil) ++ (Pp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPRPpalphamtmp;try rewrite HT2 in HPRPpalphamtmp.
	assert(HT := rule_4 (P :: R :: alpha :: nil) (Pp :: alpha :: nil) (alpha :: nil) 3 1 2 HPRPpalphamtmp Halphamtmp HPRalphaMtmp Hincl); apply HT.
}

assert(HPpalphaM : rk(Pp :: alpha ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HPpalphaeq HPpalphaM2).
assert(HPpalpham : rk(Pp :: alpha ::  nil) >= 1) by (solve_hyps_min HPpalphaeq HPpalpham1).
intuition.
Qed.

(* dans constructLemma(), requis par LQpalpha *)
(* dans constructLemma(), requis par LPRQpalpha *)
(* dans la couche 0 *)
Lemma LPQRQpOoalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Q :: R :: Qp :: Oo :: alpha ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRQpOoalpha requis par la preuve de (?)PQRQpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRQpOoalpha requis par la preuve de (?)PQRQpOoalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRQpOoalpham2 : rk(P :: Q :: R :: Qp :: Oo :: alpha :: nil) >= 2).
{
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Q :: Qp :: nil) (P :: Q :: R :: Qp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: Qp :: nil) (P :: Q :: R :: Qp :: Oo :: alpha :: nil) 2 2 HQQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRQpOoalpham4 : rk(P :: Q :: R :: Qp :: Oo :: alpha :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Qp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Qp :: Oo :: alpha :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

assert(HPQRQpOoalphaM : rk(P :: Q :: R :: Qp :: Oo :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRQpOoalpham : rk(P :: Q :: R :: Qp :: Oo :: alpha ::  nil) >= 1) by (solve_hyps_min HPQRQpOoalphaeq HPQRQpOoalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPRQpalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: R :: Qp :: alpha ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PRQpalpha requis par la preuve de (?)PRQpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour PQRPpQpOoalpha requis par la preuve de (?)PRQpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQpOoalpha requis par la preuve de (?)PQRPpQpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpm2 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -1 et -2*)
assert(HPQRPpQpm3 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3).
{
	assert(HRpMtmp : rk(Rp :: nil) <= 1) by (solve_hyps_max HRpeq HRpM1).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) ((P :: Q :: R :: Pp :: Qp :: nil) ++ (Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_2 (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil) (nil) 4 0 1 HPQRPpQpRpmtmp Hmtmp HRpMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQpOoalpha requis par la preuve de (?)PQRPpQpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQpOoalpha requis par la preuve de (?)PQRPpQpOoalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpOoalpham2 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPQRPpQpOoalpham3 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) >= 3).
{
	assert(HPQRPpQpmtmp : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3) by (solve_hyps_min HPQRPpQpeq HPQRPpQpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) 3 3 HPQRPpQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpOoalpham4 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour PRQpalpha requis par la preuve de (?)PRQpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRQpalpha requis par la preuve de (?)PRQpalpha pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HPRQpalphaM3 : rk(P :: R :: Qp :: alpha :: nil) <= 3).
{
	assert(HQpMtmp : rk(Qp :: nil) <= 1) by (solve_hyps_max HQpeq HQpM1).
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Qp :: nil) (P :: R :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Qp :: alpha :: nil) (Qp :: P :: R :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Qp :: P :: R :: alpha :: nil) ((Qp :: nil) ++ (P :: R :: alpha :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Qp :: nil) (P :: R :: alpha :: nil) (nil) 1 2 0 HQpMtmp HPRalphaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Oo :: alpha ::  de rang :  4 et 4 	 AiB : P ::  de rang :  1 et 1 	 A : P :: Q :: Pp :: Oo ::   de rang : 3 et 3 *)
assert(HPRQpalpham2 : rk(P :: R :: Qp :: alpha :: nil) >= 2).
{
	assert(HPQPpOoeq : rk(P :: Q :: Pp :: Oo :: nil) = 3) by (apply LPQPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQPpOoMtmp : rk(P :: Q :: Pp :: Oo :: nil) <= 3) by (solve_hyps_max HPQPpOoeq HPQPpOoM3).
	assert(HPQRPpQpOoalphamtmp : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) >= 4) by (solve_hyps_min HPQRPpQpOoalphaeq HPQRPpQpOoalpham4).
	assert(HPmtmp : rk(P :: nil) >= 1) by (solve_hyps_min HPeq HPm1).
	assert(Hincl : incl (P :: nil) (list_inter (P :: Q :: Pp :: Oo :: nil) (P :: R :: Qp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) (P :: Q :: Pp :: Oo :: P :: R :: Qp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: Pp :: Oo :: P :: R :: Qp :: alpha :: nil) ((P :: Q :: Pp :: Oo :: nil) ++ (P :: R :: Qp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpOoalphamtmp;try rewrite HT2 in HPQRPpQpOoalphamtmp.
	assert(HT := rule_4 (P :: Q :: Pp :: Oo :: nil) (P :: R :: Qp :: alpha :: nil) (P :: nil) 4 1 3 HPQRPpQpOoalphamtmp HPmtmp HPQPpOoMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 -2 et -4*)
(* ensembles concernés AUB : P :: Q :: R :: Qp :: Oo :: alpha ::  de rang :  4 et 4 	 AiB : Qp ::  de rang :  1 et 1 	 A : Q :: Qp :: Oo ::   de rang : 2 et 2 *)
assert(HPRQpalpham3 : rk(P :: R :: Qp :: alpha :: nil) >= 3).
{
	assert(HQQpOoMtmp : rk(Q :: Qp :: Oo :: nil) <= 2) by (solve_hyps_max HQQpOoeq HQQpOoM2).
	assert(HPQRQpOoalphaeq : rk(P :: Q :: R :: Qp :: Oo :: alpha :: nil) = 4) by (apply LPQRQpOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQRQpOoalphamtmp : rk(P :: Q :: R :: Qp :: Oo :: alpha :: nil) >= 4) by (solve_hyps_min HPQRQpOoalphaeq HPQRQpOoalpham4).
	assert(HQpmtmp : rk(Qp :: nil) >= 1) by (solve_hyps_min HQpeq HQpm1).
	assert(Hincl : incl (Qp :: nil) (list_inter (Q :: Qp :: Oo :: nil) (P :: R :: Qp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Qp :: Oo :: alpha :: nil) (Q :: Qp :: Oo :: P :: R :: Qp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Qp :: Oo :: P :: R :: Qp :: alpha :: nil) ((Q :: Qp :: Oo :: nil) ++ (P :: R :: Qp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRQpOoalphamtmp;try rewrite HT2 in HPQRQpOoalphamtmp.
	assert(HT := rule_4 (Q :: Qp :: Oo :: nil) (P :: R :: Qp :: alpha :: nil) (Qp :: nil) 4 1 2 HPQRQpOoalphamtmp HQpmtmp HQQpOoMtmp Hincl); apply HT.
}

assert(HPRQpalphaM : rk(P :: R :: Qp :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPRQpalpham : rk(P :: R :: Qp :: alpha ::  nil) >= 1) by (solve_hyps_min HPRQpalphaeq HPRQpalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LQpalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(Qp :: alpha ::  nil) = 2.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour Qpalpha requis par la preuve de (?)Qpalpha pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 2) *)
(* marque des antécédents AUB AiB A: 4 -2 et -4*)
(* ensembles concernés AUB : P :: R :: Qp :: alpha ::  de rang :  3 et 3 	 AiB : alpha ::  de rang :  1 et 1 	 A : P :: R :: alpha ::   de rang : 2 et 2 *)
assert(HQpalpham2 : rk(Qp :: alpha :: nil) >= 2).
{
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	assert(HPRQpalphaeq : rk(P :: R :: Qp :: alpha :: nil) = 3) by (apply LPRQpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPRQpalphamtmp : rk(P :: R :: Qp :: alpha :: nil) >= 3) by (solve_hyps_min HPRQpalphaeq HPRQpalpham3).
	assert(Halphamtmp : rk(alpha :: nil) >= 1) by (solve_hyps_min Halphaeq Halpham1).
	assert(Hincl : incl (alpha :: nil) (list_inter (P :: R :: alpha :: nil) (Qp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Qp :: alpha :: nil) (P :: R :: alpha :: Qp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: alpha :: Qp :: alpha :: nil) ((P :: R :: alpha :: nil) ++ (Qp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPRQpalphamtmp;try rewrite HT2 in HPRQpalphamtmp.
	assert(HT := rule_4 (P :: R :: alpha :: nil) (Qp :: alpha :: nil) (alpha :: nil) 3 1 2 HPRQpalphamtmp Halphamtmp HPRalphaMtmp Hincl); apply HT.
}

assert(HQpalphaM : rk(Qp :: alpha ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HQpalphaeq HQpalphaM2).
assert(HQpalpham : rk(Qp :: alpha ::  nil) >= 1) by (solve_hyps_min HQpalphaeq HQpalpham1).
intuition.
Qed.

(* dans constructLemma(), requis par LPpQpalpha *)
(* dans la couche 0 *)
Lemma LPpQpRpOoalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(Pp :: Qp :: Rp :: Oo :: alpha ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PpQpRpOoalpha requis par la preuve de (?)PpQpRpOoalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPpQpRpOoalpham4 : rk(Pp :: Qp :: Rp :: Oo :: alpha :: nil) >= 4).
{
	assert(HPpQpRpOomtmp : rk(Pp :: Qp :: Rp :: Oo :: nil) >= 4) by (solve_hyps_min HPpQpRpOoeq HPpQpRpOom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: Rp :: Oo :: nil) (Pp :: Qp :: Rp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: Rp :: Oo :: nil) (Pp :: Qp :: Rp :: Oo :: alpha :: nil) 4 4 HPpQpRpOomtmp Hcomp Hincl);apply HT.
}

assert(HPpQpRpOoalphaM : rk(Pp :: Qp :: Rp :: Oo :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPpQpRpOoalpham : rk(Pp :: Qp :: Rp :: Oo :: alpha ::  nil) >= 1) by (solve_hyps_min HPpQpRpOoalphaeq HPpQpRpOoalpham1).
intuition.
Qed.

(* dans constructLemma(), requis par LPpQpalpha *)
(* dans la couche 0 *)
Lemma LPpRpOoalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(Pp :: Rp :: Oo :: alpha ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PpRpOoalpha requis par la preuve de (?)PpRpOoalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 3 pour PRPpRpOoalpha requis par la preuve de (?)PpRpOoalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 3 pour PRPpOoalpha requis par la preuve de (?)PRPpRpOoalpha pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PRPpOoalpha requis par la preuve de (?)PRPpOoalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpOoalpha requis par la preuve de (?)PRPpOoalpha pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpOoalpha requis par la preuve de (?)PRPpOoalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPRPpOoalpham2 : rk(P :: R :: Pp :: Oo :: alpha :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Oo :: alpha :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -2*)
assert(HPRPpOoalphaM3 : rk(P :: R :: Pp :: Oo :: alpha :: nil) <= 3).
{
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	assert(HPmtmp : rk(P :: nil) >= 1) by (solve_hyps_min HPeq HPm1).
	assert(Hincl : incl (P :: nil) (list_inter (P :: Pp :: Oo :: nil) (P :: R :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: Oo :: alpha :: nil) (P :: Pp :: Oo :: P :: R :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Oo :: P :: R :: alpha :: nil) ((P :: Pp :: Oo :: nil) ++ (P :: R :: alpha :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P :: Pp :: Oo :: nil) (P :: R :: alpha :: nil) (P :: nil) 2 2 1 HPPpOoMtmp HPRalphaMtmp HPmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 -4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Oo :: alpha ::  de rang :  4 et 4 	 AiB : P :: Pp :: Oo ::  de rang :  2 et 2 	 A : P :: Q :: Pp :: Oo ::   de rang : 3 et 3 *)
assert(HPRPpOoalpham3 : rk(P :: R :: Pp :: Oo :: alpha :: nil) >= 3).
{
	assert(HPQPpOoeq : rk(P :: Q :: Pp :: Oo :: nil) = 3) by (apply LPQPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQPpOoMtmp : rk(P :: Q :: Pp :: Oo :: nil) <= 3) by (solve_hyps_max HPQPpOoeq HPQPpOoM3).
	assert(HPQRPpOoalphaeq : rk(P :: Q :: R :: Pp :: Oo :: alpha :: nil) = 4) by (apply LPQRPpOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQRPpOoalphamtmp : rk(P :: Q :: R :: Pp :: Oo :: alpha :: nil) >= 4) by (solve_hyps_min HPQRPpOoalphaeq HPQRPpOoalpham4).
	assert(HPPpOomtmp : rk(P :: Pp :: Oo :: nil) >= 2) by (solve_hyps_min HPPpOoeq HPPpOom2).
	assert(Hincl : incl (P :: Pp :: Oo :: nil) (list_inter (P :: Q :: Pp :: Oo :: nil) (P :: R :: Pp :: Oo :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Oo :: alpha :: nil) (P :: Q :: Pp :: Oo :: P :: R :: Pp :: Oo :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: Pp :: Oo :: P :: R :: Pp :: Oo :: alpha :: nil) ((P :: Q :: Pp :: Oo :: nil) ++ (P :: R :: Pp :: Oo :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpOoalphamtmp;try rewrite HT2 in HPQRPpOoalphamtmp.
	assert(HT := rule_4 (P :: Q :: Pp :: Oo :: nil) (P :: R :: Pp :: Oo :: alpha :: nil) (P :: Pp :: Oo :: nil) 4 2 3 HPQRPpOoalphamtmp HPPpOomtmp HPQPpOoMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRPpRpOoalpha requis par la preuve de (?)PRPpRpOoalpha pour la règle 1  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour PQRPpRpOoalpha requis par la preuve de (?)PRPpRpOoalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpRpOoalpha requis par la preuve de (?)PQRPpRpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpRp requis par la preuve de (?)PQRPpRpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpRp requis par la preuve de (?)PQRPpRp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpRp requis par la preuve de (?)PQRPpRp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpRpm2 : rk(P :: Q :: R :: Pp :: Rp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Rp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Rp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: -4 -1 et -2*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Rp ::  de rang :  4 et 4 	 AiB :  de rang :  0 et 0 	 A : Qp ::   de rang : 1 et 1 *)
assert(HPQRPpRpm3 : rk(P :: Q :: R :: Pp :: Rp :: nil) >= 3).
{
	assert(HQpMtmp : rk(Qp :: nil) <= 1) by (solve_hyps_max HQpeq HQpM1).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Qp :: nil) (P :: Q :: R :: Pp :: Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (Qp :: P :: Q :: R :: Pp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Qp :: P :: Q :: R :: Pp :: Rp :: nil) ((Qp :: nil) ++ (P :: Q :: R :: Pp :: Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_4 (Qp :: nil) (P :: Q :: R :: Pp :: Rp :: nil) (nil) 4 0 1 HPQRPpQpRpmtmp Hmtmp HQpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpRpOoalpha requis par la preuve de (?)PQRPpRpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpRpOoalpha requis par la preuve de (?)PQRPpRpOoalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpRpOoalpham2 : rk(P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPQRPpRpOoalpham3 : rk(P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil) >= 3).
{
	assert(HPQRPpRpmtmp : rk(P :: Q :: R :: Pp :: Rp :: nil) >= 3) by (solve_hyps_min HPQRPpRpeq HPQRPpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Pp :: Rp :: nil) (P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Pp :: Rp :: nil) (P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil) 3 3 HPQRPpRpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpRpOoalpham4 : rk(P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpRpOoalpha requis par la preuve de (?)PRPpRpOoalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpRpOoalpha requis par la preuve de (?)PRPpRpOoalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPRPpRpOoalpham2 : rk(P :: R :: Pp :: Rp :: Oo :: alpha :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Rp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Rp :: Oo :: alpha :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Rp :: Oo :: alpha ::  de rang :  4 et 4 	 AiB : P :: Pp :: Oo ::  de rang :  2 et 2 	 A : P :: Q :: Pp :: Oo ::   de rang : 3 et 3 *)
assert(HPRPpRpOoalpham3 : rk(P :: R :: Pp :: Rp :: Oo :: alpha :: nil) >= 3).
{
	assert(HPQPpOoeq : rk(P :: Q :: Pp :: Oo :: nil) = 3) by (apply LPQPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQPpOoMtmp : rk(P :: Q :: Pp :: Oo :: nil) <= 3) by (solve_hyps_max HPQPpOoeq HPQPpOoM3).
	assert(HPQRPpRpOoalphamtmp : rk(P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil) >= 4) by (solve_hyps_min HPQRPpRpOoalphaeq HPQRPpRpOoalpham4).
	assert(HPPpOomtmp : rk(P :: Pp :: Oo :: nil) >= 2) by (solve_hyps_min HPPpOoeq HPPpOom2).
	assert(Hincl : incl (P :: Pp :: Oo :: nil) (list_inter (P :: Q :: Pp :: Oo :: nil) (P :: R :: Pp :: Rp :: Oo :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil) (P :: Q :: Pp :: Oo :: P :: R :: Pp :: Rp :: Oo :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: Pp :: Oo :: P :: R :: Pp :: Rp :: Oo :: alpha :: nil) ((P :: Q :: Pp :: Oo :: nil) ++ (P :: R :: Pp :: Rp :: Oo :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpRpOoalphamtmp;try rewrite HT2 in HPQRPpRpOoalphamtmp.
	assert(HT := rule_4 (P :: Q :: Pp :: Oo :: nil) (P :: R :: Pp :: Rp :: Oo :: alpha :: nil) (P :: Pp :: Oo :: nil) 4 2 3 HPQRPpRpOoalphamtmp HPPpOomtmp HPQPpOoMtmp Hincl); apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 5 et 4*)
assert(HPRPpRpOoalphaM3 : rk(P :: R :: Pp :: Rp :: Oo :: alpha :: nil) <= 3).
{
	assert(HPRPpRpOoeq : rk(P :: R :: Pp :: Rp :: Oo :: nil) = 3) by (apply LPRPpRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPRPpRpOoMtmp : rk(P :: R :: Pp :: Rp :: Oo :: nil) <= 3) by (solve_hyps_max HPRPpRpOoeq HPRPpRpOoM3).
	assert(HPRPpOoalphaMtmp : rk(P :: R :: Pp :: Oo :: alpha :: nil) <= 3) by (solve_hyps_max HPRPpOoalphaeq HPRPpOoalphaM3).
	assert(HPRPpOoeq : rk(P :: R :: Pp :: Oo :: nil) = 3) by (apply LPRPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPRPpOomtmp : rk(P :: R :: Pp :: Oo :: nil) >= 3) by (solve_hyps_min HPRPpOoeq HPRPpOom3).
	assert(Hincl : incl (P :: R :: Pp :: Oo :: nil) (list_inter (P :: R :: Pp :: Rp :: Oo :: nil) (P :: R :: Pp :: Oo :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: Rp :: Oo :: alpha :: nil) (P :: R :: Pp :: Rp :: Oo :: P :: R :: Pp :: Oo :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: Pp :: Rp :: Oo :: P :: R :: Pp :: Oo :: alpha :: nil) ((P :: R :: Pp :: Rp :: Oo :: nil) ++ (P :: R :: Pp :: Oo :: alpha :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P :: R :: Pp :: Rp :: Oo :: nil) (P :: R :: Pp :: Oo :: alpha :: nil) (P :: R :: Pp :: Oo :: nil) 3 3 3 HPRPpRpOoMtmp HPRPpOoalphaMtmp HPRPpOomtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour PpRpOoalpha requis par la preuve de (?)PpRpOoalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PpRpOoalpha requis par la preuve de (?)PpRpOoalpha pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HPpRpOoalphaM3 : rk(Pp :: Rp :: Oo :: alpha :: nil) <= 3).
{
	assert(HOoMtmp : rk(Oo :: nil) <= 1) by (solve_hyps_max HOoeq HOoM1).
	assert(HPpRpalphaMtmp : rk(Pp :: Rp :: alpha :: nil) <= 2) by (solve_hyps_max HPpRpalphaeq HPpRpalphaM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Oo :: nil) (Pp :: Rp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Pp :: Rp :: Oo :: alpha :: nil) (Oo :: Pp :: Rp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: Pp :: Rp :: alpha :: nil) ((Oo :: nil) ++ (Pp :: Rp :: alpha :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Oo :: nil) (Pp :: Rp :: alpha :: nil) (nil) 1 2 0 HOoMtmp HPpRpalphaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : P :: R :: Pp :: Rp :: Oo :: alpha ::  de rang :  3 et 3 	 AiB : alpha ::  de rang :  1 et 1 	 A : P :: R :: alpha ::   de rang : 2 et 2 *)
assert(HPpRpOoalpham2 : rk(Pp :: Rp :: Oo :: alpha :: nil) >= 2).
{
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	assert(HPRPpRpOoalphamtmp : rk(P :: R :: Pp :: Rp :: Oo :: alpha :: nil) >= 3) by (solve_hyps_min HPRPpRpOoalphaeq HPRPpRpOoalpham3).
	assert(Halphamtmp : rk(alpha :: nil) >= 1) by (solve_hyps_min Halphaeq Halpham1).
	assert(Hincl : incl (alpha :: nil) (list_inter (P :: R :: alpha :: nil) (Pp :: Rp :: Oo :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: Rp :: Oo :: alpha :: nil) (P :: R :: alpha :: Pp :: Rp :: Oo :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: alpha :: Pp :: Rp :: Oo :: alpha :: nil) ((P :: R :: alpha :: nil) ++ (Pp :: Rp :: Oo :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPRPpRpOoalphamtmp;try rewrite HT2 in HPRPpRpOoalphamtmp.
	assert(HT := rule_4 (P :: R :: alpha :: nil) (Pp :: Rp :: Oo :: alpha :: nil) (alpha :: nil) 3 1 2 HPRPpRpOoalphamtmp Halphamtmp HPRalphaMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 -2 et 4*)
(* ensembles concernés AUB : Pp :: Qp :: Rp :: Oo :: alpha ::  de rang :  4 et 4 	 AiB : alpha ::  de rang :  1 et 1 	 A : Qp :: alpha ::   de rang : 2 et 2 *)
assert(HPpRpOoalpham3 : rk(Pp :: Rp :: Oo :: alpha :: nil) >= 3).
{
	assert(HQpalphaeq : rk(Qp :: alpha :: nil) = 2) by (apply LQpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HQpalphaMtmp : rk(Qp :: alpha :: nil) <= 2) by (solve_hyps_max HQpalphaeq HQpalphaM2).
	assert(HPpQpRpOoalphaeq : rk(Pp :: Qp :: Rp :: Oo :: alpha :: nil) = 4) by (apply LPpQpRpOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpQpRpOoalphamtmp : rk(Pp :: Qp :: Rp :: Oo :: alpha :: nil) >= 4) by (solve_hyps_min HPpQpRpOoalphaeq HPpQpRpOoalpham4).
	assert(Halphamtmp : rk(alpha :: nil) >= 1) by (solve_hyps_min Halphaeq Halpham1).
	assert(Hincl : incl (alpha :: nil) (list_inter (Qp :: alpha :: nil) (Pp :: Rp :: Oo :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Pp :: Qp :: Rp :: Oo :: alpha :: nil) (Qp :: alpha :: Pp :: Rp :: Oo :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Qp :: alpha :: Pp :: Rp :: Oo :: alpha :: nil) ((Qp :: alpha :: nil) ++ (Pp :: Rp :: Oo :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPpQpRpOoalphamtmp;try rewrite HT2 in HPpQpRpOoalphamtmp.
	assert(HT := rule_4 (Qp :: alpha :: nil) (Pp :: Rp :: Oo :: alpha :: nil) (alpha :: nil) 4 1 2 HPpQpRpOoalphamtmp Halphamtmp HQpalphaMtmp Hincl); apply HT.
}

assert(HPpRpOoalphaM : rk(Pp :: Rp :: Oo :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPpRpOoalpham : rk(Pp :: Rp :: Oo :: alpha ::  nil) >= 1) by (solve_hyps_min HPpRpOoalphaeq HPpRpOoalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPpQpalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(Pp :: Qp :: alpha ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PpQpalpha requis par la preuve de (?)PpQpalpha pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRPpQpalpha requis par la preuve de (?)PpQpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour PQRPpQpOoalpha requis par la preuve de (?)PRPpQpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQpOoalpha requis par la preuve de (?)PQRPpQpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpm2 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -1 et -2*)
assert(HPQRPpQpm3 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3).
{
	assert(HRpMtmp : rk(Rp :: nil) <= 1) by (solve_hyps_max HRpeq HRpM1).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) ((P :: Q :: R :: Pp :: Qp :: nil) ++ (Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_2 (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil) (nil) 4 0 1 HPQRPpQpRpmtmp Hmtmp HRpMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQpOoalpha requis par la preuve de (?)PQRPpQpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQpOoalpha requis par la preuve de (?)PQRPpQpOoalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpOoalpham2 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPQRPpQpOoalpham3 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) >= 3).
{
	assert(HPQRPpQpmtmp : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3) by (solve_hyps_min HPQRPpQpeq HPQRPpQpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) 3 3 HPQRPpQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpOoalpham4 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpQpalpha requis par la preuve de (?)PRPpQpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpQpalpha requis par la preuve de (?)PRPpQpalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPRPpQpalpham2 : rk(P :: R :: Pp :: Qp :: alpha :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Qp :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Qp :: alpha :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Oo :: alpha ::  de rang :  4 et 4 	 AiB : P :: Pp ::  de rang :  2 et 2 	 A : P :: Q :: Pp :: Oo ::   de rang : 3 et 3 *)
assert(HPRPpQpalpham3 : rk(P :: R :: Pp :: Qp :: alpha :: nil) >= 3).
{
	assert(HPQPpOoeq : rk(P :: Q :: Pp :: Oo :: nil) = 3) by (apply LPQPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQPpOoMtmp : rk(P :: Q :: Pp :: Oo :: nil) <= 3) by (solve_hyps_max HPQPpOoeq HPQPpOoM3).
	assert(HPQRPpQpOoalphamtmp : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) >= 4) by (solve_hyps_min HPQRPpQpOoalphaeq HPQRPpQpOoalpham4).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hincl : incl (P :: Pp :: nil) (list_inter (P :: Q :: Pp :: Oo :: nil) (P :: R :: Pp :: Qp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) (P :: Q :: Pp :: Oo :: P :: R :: Pp :: Qp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: Pp :: Oo :: P :: R :: Pp :: Qp :: alpha :: nil) ((P :: Q :: Pp :: Oo :: nil) ++ (P :: R :: Pp :: Qp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpOoalphamtmp;try rewrite HT2 in HPQRPpQpOoalphamtmp.
	assert(HT := rule_4 (P :: Q :: Pp :: Oo :: nil) (P :: R :: Pp :: Qp :: alpha :: nil) (P :: Pp :: nil) 4 2 3 HPQRPpQpOoalphamtmp HPPpmtmp HPQPpOoMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour PpQpalpha requis par la preuve de (?)PpQpalpha pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : P :: R :: Pp :: Qp :: alpha ::  de rang :  3 et 4 	 AiB : alpha ::  de rang :  1 et 1 	 A : P :: R :: alpha ::   de rang : 2 et 2 *)
assert(HPpQpalpham2 : rk(Pp :: Qp :: alpha :: nil) >= 2).
{
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	assert(HPRPpQpalphamtmp : rk(P :: R :: Pp :: Qp :: alpha :: nil) >= 3) by (solve_hyps_min HPRPpQpalphaeq HPRPpQpalpham3).
	assert(Halphamtmp : rk(alpha :: nil) >= 1) by (solve_hyps_min Halphaeq Halpham1).
	assert(Hincl : incl (alpha :: nil) (list_inter (P :: R :: alpha :: nil) (Pp :: Qp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: Qp :: alpha :: nil) (P :: R :: alpha :: Pp :: Qp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: alpha :: Pp :: Qp :: alpha :: nil) ((P :: R :: alpha :: nil) ++ (Pp :: Qp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPRPpQpalphamtmp;try rewrite HT2 in HPRPpQpalphamtmp.
	assert(HT := rule_4 (P :: R :: alpha :: nil) (Pp :: Qp :: alpha :: nil) (alpha :: nil) 3 1 2 HPRPpQpalphamtmp Halphamtmp HPRalphaMtmp Hincl); apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 4*)
assert(HPpQpalpham3 : rk(Pp :: Qp :: alpha :: nil) >= 3).
{
	assert(HPpRpOoalphaeq : rk(Pp :: Rp :: Oo :: alpha :: nil) = 3) by (apply LPpRpOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpRpOoalphaMtmp : rk(Pp :: Rp :: Oo :: alpha :: nil) <= 3) by (solve_hyps_max HPpRpOoalphaeq HPpRpOoalphaM3).
	assert(HPpQpRpOoalphaeq : rk(Pp :: Qp :: Rp :: Oo :: alpha :: nil) = 4) by (apply LPpQpRpOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpQpRpOoalphamtmp : rk(Pp :: Qp :: Rp :: Oo :: alpha :: nil) >= 4) by (solve_hyps_min HPpQpRpOoalphaeq HPpQpRpOoalpham4).
	assert(HPpalphaeq : rk(Pp :: alpha :: nil) = 2) by (apply LPpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpalphamtmp : rk(Pp :: alpha :: nil) >= 2) by (solve_hyps_min HPpalphaeq HPpalpham2).
	assert(Hincl : incl (Pp :: alpha :: nil) (list_inter (Pp :: Qp :: alpha :: nil) (Pp :: Rp :: Oo :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Pp :: Qp :: Rp :: Oo :: alpha :: nil) (Pp :: Qp :: alpha :: Pp :: Rp :: Oo :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: Qp :: alpha :: Pp :: Rp :: Oo :: alpha :: nil) ((Pp :: Qp :: alpha :: nil) ++ (Pp :: Rp :: Oo :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPpQpRpOoalphamtmp;try rewrite HT2 in HPpQpRpOoalphamtmp.
	assert(HT := rule_2 (Pp :: Qp :: alpha :: nil) (Pp :: Rp :: Oo :: alpha :: nil) (Pp :: alpha :: nil) 4 2 3 HPpQpRpOoalphamtmp HPpalphamtmp HPpRpOoalphaMtmp Hincl);apply HT.
}

assert(HPpQpalphaM : rk(Pp :: Qp :: alpha ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HPpQpalphaeq HPpQpalphaM3).
assert(HPpQpalpham : rk(Pp :: Qp :: alpha ::  nil) >= 1) by (solve_hyps_min HPpQpalphaeq HPpQpalpham1).
intuition.
Qed.

(* dans constructLemma(), requis par LPRPpQpalpha *)
(* dans la couche 0 *)
Lemma LPRPpQpRpOoalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: R :: Pp :: Qp :: Rp :: Oo :: alpha ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRPpQpRpOoalpha requis par la preuve de (?)PRPpQpRpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRPpQpRp requis par la preuve de (?)PRPpQpRpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour QPp requis par la preuve de (?)PRPpQpRp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpQpRp requis par la preuve de (?)PRPpQpRp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpQpRp requis par la preuve de (?)PRPpQpRp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPRPpQpRpm2 : rk(P :: R :: Pp :: Qp :: Rp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: -4 -2 et 5*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Rp ::  de rang :  4 et 4 	 AiB : Pp ::  de rang :  1 et 1 	 A : Q :: Pp ::   de rang : 1 et 2 *)
assert(HPRPpQpRpm3 : rk(P :: R :: Pp :: Qp :: Rp :: nil) >= 3).
{
	assert(HQPpMtmp : rk(Q :: Pp :: nil) <= 2) by (solve_hyps_max HQPpeq HQPpM2).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(HPpmtmp : rk(Pp :: nil) >= 1) by (solve_hyps_min HPpeq HPpm1).
	assert(Hincl : incl (Pp :: nil) (list_inter (Q :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (Q :: Pp :: P :: R :: Pp :: Qp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Pp :: P :: R :: Pp :: Qp :: Rp :: nil) ((Q :: Pp :: nil) ++ (P :: R :: Pp :: Qp :: Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_4 (Q :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: nil) (Pp :: nil) 4 1 2 HPQRPpQpRpmtmp HPpmtmp HQPpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpQpRpOoalpha requis par la preuve de (?)PRPpQpRpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpQpRpOoalpha requis par la preuve de (?)PRPpQpRpOoalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPRPpQpRpOoalpham2 : rk(P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPRPpQpRpOoalpham3 : rk(P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: nil) >= 3).
{
	assert(HPRPpQpRpmtmp : rk(P :: R :: Pp :: Qp :: Rp :: nil) >= 3) by (solve_hyps_min HPRPpQpRpeq HPRPpQpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: R :: Pp :: Qp :: Rp :: nil) (P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: R :: Pp :: Qp :: Rp :: nil) (P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: nil) 3 3 HPRPpQpRpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPRPpQpRpOoalpham4 : rk(P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: nil) >= 4).
{
	assert(HPpQpRpOomtmp : rk(Pp :: Qp :: Rp :: Oo :: nil) >= 4) by (solve_hyps_min HPpQpRpOoeq HPpQpRpOom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: Rp :: Oo :: nil) (P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: Rp :: Oo :: nil) (P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: nil) 4 4 HPpQpRpOomtmp Hcomp Hincl);apply HT.
}

assert(HPRPpQpRpOoalphaM : rk(P :: R :: Pp :: Qp :: Rp :: Oo :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPRPpQpRpOoalpham : rk(P :: R :: Pp :: Qp :: Rp :: Oo :: alpha ::  nil) >= 1) by (solve_hyps_min HPRPpQpRpOoalphaeq HPRPpQpRpOoalpham1).
intuition.
Qed.

(* dans constructLemma(), requis par LPRPpQpalpha *)
(* dans constructLemma(), requis par LPRPpRpOoalpha *)
(* dans la couche 0 *)
Lemma LPRPpOoalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: R :: Pp :: Oo :: alpha ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PRPpOoalpha requis par la preuve de (?)PRPpOoalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpOoalpha requis par la preuve de (?)PRPpOoalpha pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpOoalpha requis par la preuve de (?)PRPpOoalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPRPpOoalpham2 : rk(P :: R :: Pp :: Oo :: alpha :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Oo :: alpha :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -2*)
assert(HPRPpOoalphaM3 : rk(P :: R :: Pp :: Oo :: alpha :: nil) <= 3).
{
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	assert(HPmtmp : rk(P :: nil) >= 1) by (solve_hyps_min HPeq HPm1).
	assert(Hincl : incl (P :: nil) (list_inter (P :: Pp :: Oo :: nil) (P :: R :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: Oo :: alpha :: nil) (P :: Pp :: Oo :: P :: R :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Oo :: P :: R :: alpha :: nil) ((P :: Pp :: Oo :: nil) ++ (P :: R :: alpha :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P :: Pp :: Oo :: nil) (P :: R :: alpha :: nil) (P :: nil) 2 2 1 HPPpOoMtmp HPRalphaMtmp HPmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 -4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Oo :: alpha ::  de rang :  4 et 4 	 AiB : P :: Pp :: Oo ::  de rang :  2 et 2 	 A : P :: Q :: Pp :: Oo ::   de rang : 3 et 3 *)
assert(HPRPpOoalpham3 : rk(P :: R :: Pp :: Oo :: alpha :: nil) >= 3).
{
	assert(HPQPpOoeq : rk(P :: Q :: Pp :: Oo :: nil) = 3) by (apply LPQPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQPpOoMtmp : rk(P :: Q :: Pp :: Oo :: nil) <= 3) by (solve_hyps_max HPQPpOoeq HPQPpOoM3).
	assert(HPQRPpOoalphaeq : rk(P :: Q :: R :: Pp :: Oo :: alpha :: nil) = 4) by (apply LPQRPpOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQRPpOoalphamtmp : rk(P :: Q :: R :: Pp :: Oo :: alpha :: nil) >= 4) by (solve_hyps_min HPQRPpOoalphaeq HPQRPpOoalpham4).
	assert(HPPpOomtmp : rk(P :: Pp :: Oo :: nil) >= 2) by (solve_hyps_min HPPpOoeq HPPpOom2).
	assert(Hincl : incl (P :: Pp :: Oo :: nil) (list_inter (P :: Q :: Pp :: Oo :: nil) (P :: R :: Pp :: Oo :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Oo :: alpha :: nil) (P :: Q :: Pp :: Oo :: P :: R :: Pp :: Oo :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: Pp :: Oo :: P :: R :: Pp :: Oo :: alpha :: nil) ((P :: Q :: Pp :: Oo :: nil) ++ (P :: R :: Pp :: Oo :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpOoalphamtmp;try rewrite HT2 in HPQRPpOoalphamtmp.
	assert(HT := rule_4 (P :: Q :: Pp :: Oo :: nil) (P :: R :: Pp :: Oo :: alpha :: nil) (P :: Pp :: Oo :: nil) 4 2 3 HPQRPpOoalphamtmp HPPpOomtmp HPQPpOoMtmp Hincl); apply HT.
}

assert(HPRPpOoalphaM : rk(P :: R :: Pp :: Oo :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPRPpOoalpham : rk(P :: R :: Pp :: Oo :: alpha ::  nil) >= 1) by (solve_hyps_min HPRPpOoalphaeq HPRPpOoalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPRPpRpOoalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: R :: Pp :: Rp :: Oo :: alpha ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRPpRpOoalpha requis par la preuve de (?)PRPpRpOoalpha pour la règle 1  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour PQRPpRpOoalpha requis par la preuve de (?)PRPpRpOoalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpRpOoalpha requis par la preuve de (?)PQRPpRpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpRp requis par la preuve de (?)PQRPpRpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpRp requis par la preuve de (?)PQRPpRp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpRp requis par la preuve de (?)PQRPpRp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpRpm2 : rk(P :: Q :: R :: Pp :: Rp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Rp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Rp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: -4 -1 et -2*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Rp ::  de rang :  4 et 4 	 AiB :  de rang :  0 et 0 	 A : Qp ::   de rang : 1 et 1 *)
assert(HPQRPpRpm3 : rk(P :: Q :: R :: Pp :: Rp :: nil) >= 3).
{
	assert(HQpMtmp : rk(Qp :: nil) <= 1) by (solve_hyps_max HQpeq HQpM1).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Qp :: nil) (P :: Q :: R :: Pp :: Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (Qp :: P :: Q :: R :: Pp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Qp :: P :: Q :: R :: Pp :: Rp :: nil) ((Qp :: nil) ++ (P :: Q :: R :: Pp :: Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_4 (Qp :: nil) (P :: Q :: R :: Pp :: Rp :: nil) (nil) 4 0 1 HPQRPpQpRpmtmp Hmtmp HQpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpRpOoalpha requis par la preuve de (?)PQRPpRpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpRpOoalpha requis par la preuve de (?)PQRPpRpOoalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpRpOoalpham2 : rk(P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPQRPpRpOoalpham3 : rk(P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil) >= 3).
{
	assert(HPQRPpRpmtmp : rk(P :: Q :: R :: Pp :: Rp :: nil) >= 3) by (solve_hyps_min HPQRPpRpeq HPQRPpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Pp :: Rp :: nil) (P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Pp :: Rp :: nil) (P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil) 3 3 HPQRPpRpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpRpOoalpham4 : rk(P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpRpOoalpha requis par la preuve de (?)PRPpRpOoalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpRpOoalpha requis par la preuve de (?)PRPpRpOoalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPRPpRpOoalpham2 : rk(P :: R :: Pp :: Rp :: Oo :: alpha :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Rp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Rp :: Oo :: alpha :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Rp :: Oo :: alpha ::  de rang :  4 et 4 	 AiB : P :: Pp :: Oo ::  de rang :  2 et 2 	 A : P :: Q :: Pp :: Oo ::   de rang : 3 et 3 *)
assert(HPRPpRpOoalpham3 : rk(P :: R :: Pp :: Rp :: Oo :: alpha :: nil) >= 3).
{
	assert(HPQPpOoeq : rk(P :: Q :: Pp :: Oo :: nil) = 3) by (apply LPQPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQPpOoMtmp : rk(P :: Q :: Pp :: Oo :: nil) <= 3) by (solve_hyps_max HPQPpOoeq HPQPpOoM3).
	assert(HPQRPpRpOoalphamtmp : rk(P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil) >= 4) by (solve_hyps_min HPQRPpRpOoalphaeq HPQRPpRpOoalpham4).
	assert(HPPpOomtmp : rk(P :: Pp :: Oo :: nil) >= 2) by (solve_hyps_min HPPpOoeq HPPpOom2).
	assert(Hincl : incl (P :: Pp :: Oo :: nil) (list_inter (P :: Q :: Pp :: Oo :: nil) (P :: R :: Pp :: Rp :: Oo :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil) (P :: Q :: Pp :: Oo :: P :: R :: Pp :: Rp :: Oo :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: Pp :: Oo :: P :: R :: Pp :: Rp :: Oo :: alpha :: nil) ((P :: Q :: Pp :: Oo :: nil) ++ (P :: R :: Pp :: Rp :: Oo :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpRpOoalphamtmp;try rewrite HT2 in HPQRPpRpOoalphamtmp.
	assert(HT := rule_4 (P :: Q :: Pp :: Oo :: nil) (P :: R :: Pp :: Rp :: Oo :: alpha :: nil) (P :: Pp :: Oo :: nil) 4 2 3 HPQRPpRpOoalphamtmp HPPpOomtmp HPQPpOoMtmp Hincl); apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HPRPpRpOoalphaM3 : rk(P :: R :: Pp :: Rp :: Oo :: alpha :: nil) <= 3).
{
	assert(HPRPpRpOoeq : rk(P :: R :: Pp :: Rp :: Oo :: nil) = 3) by (apply LPRPpRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPRPpRpOoMtmp : rk(P :: R :: Pp :: Rp :: Oo :: nil) <= 3) by (solve_hyps_max HPRPpRpOoeq HPRPpRpOoM3).
	assert(HPRPpOoalphaeq : rk(P :: R :: Pp :: Oo :: alpha :: nil) = 3) by (apply LPRPpOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPRPpOoalphaMtmp : rk(P :: R :: Pp :: Oo :: alpha :: nil) <= 3) by (solve_hyps_max HPRPpOoalphaeq HPRPpOoalphaM3).
	assert(HPRPpOoeq : rk(P :: R :: Pp :: Oo :: nil) = 3) by (apply LPRPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPRPpOomtmp : rk(P :: R :: Pp :: Oo :: nil) >= 3) by (solve_hyps_min HPRPpOoeq HPRPpOom3).
	assert(Hincl : incl (P :: R :: Pp :: Oo :: nil) (list_inter (P :: R :: Pp :: Rp :: Oo :: nil) (P :: R :: Pp :: Oo :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: Rp :: Oo :: alpha :: nil) (P :: R :: Pp :: Rp :: Oo :: P :: R :: Pp :: Oo :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: Pp :: Rp :: Oo :: P :: R :: Pp :: Oo :: alpha :: nil) ((P :: R :: Pp :: Rp :: Oo :: nil) ++ (P :: R :: Pp :: Oo :: alpha :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P :: R :: Pp :: Rp :: Oo :: nil) (P :: R :: Pp :: Oo :: alpha :: nil) (P :: R :: Pp :: Oo :: nil) 3 3 3 HPRPpRpOoMtmp HPRPpOoalphaMtmp HPRPpOomtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HPRPpRpOoalphaM : rk(P :: R :: Pp :: Rp :: Oo :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPRPpRpOoalpham : rk(P :: R :: Pp :: Rp :: Oo :: alpha ::  nil) >= 1) by (solve_hyps_min HPRPpRpOoalphaeq HPRPpRpOoalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPRPpQpalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: R :: Pp :: Qp :: alpha ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRPpQpalpha requis par la preuve de (?)PRPpQpalpha pour la règle 2  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour PQRPpQpOoalpha requis par la preuve de (?)PRPpQpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQpOoalpha requis par la preuve de (?)PQRPpQpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpm2 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -1 et -2*)
assert(HPQRPpQpm3 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3).
{
	assert(HRpMtmp : rk(Rp :: nil) <= 1) by (solve_hyps_max HRpeq HRpM1).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) ((P :: Q :: R :: Pp :: Qp :: nil) ++ (Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_2 (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil) (nil) 4 0 1 HPQRPpQpRpmtmp Hmtmp HRpMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQpOoalpha requis par la preuve de (?)PQRPpQpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQpOoalpha requis par la preuve de (?)PQRPpQpOoalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpOoalpham2 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPQRPpQpOoalpham3 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) >= 3).
{
	assert(HPQRPpQpmtmp : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3) by (solve_hyps_min HPQRPpQpeq HPQRPpQpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) 3 3 HPQRPpQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpOoalpham4 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpQpalpha requis par la preuve de (?)PRPpQpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpQpalpha requis par la preuve de (?)PRPpQpalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPRPpQpalpham2 : rk(P :: R :: Pp :: Qp :: alpha :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Qp :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Qp :: alpha :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Oo :: alpha ::  de rang :  4 et 4 	 AiB : P :: Pp ::  de rang :  2 et 2 	 A : P :: Q :: Pp :: Oo ::   de rang : 3 et 3 *)
assert(HPRPpQpalpham3 : rk(P :: R :: Pp :: Qp :: alpha :: nil) >= 3).
{
	assert(HPQPpOoeq : rk(P :: Q :: Pp :: Oo :: nil) = 3) by (apply LPQPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQPpOoMtmp : rk(P :: Q :: Pp :: Oo :: nil) <= 3) by (solve_hyps_max HPQPpOoeq HPQPpOoM3).
	assert(HPQRPpQpOoalphamtmp : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) >= 4) by (solve_hyps_min HPQRPpQpOoalphaeq HPQRPpQpOoalpham4).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hincl : incl (P :: Pp :: nil) (list_inter (P :: Q :: Pp :: Oo :: nil) (P :: R :: Pp :: Qp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) (P :: Q :: Pp :: Oo :: P :: R :: Pp :: Qp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: Pp :: Oo :: P :: R :: Pp :: Qp :: alpha :: nil) ((P :: Q :: Pp :: Oo :: nil) ++ (P :: R :: Pp :: Qp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpOoalphamtmp;try rewrite HT2 in HPQRPpQpOoalphamtmp.
	assert(HT := rule_4 (P :: Q :: Pp :: Oo :: nil) (P :: R :: Pp :: Qp :: alpha :: nil) (P :: Pp :: nil) 4 2 3 HPQRPpQpOoalphamtmp HPPpmtmp HPQPpOoMtmp Hincl); apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 4*)
assert(HPRPpQpalpham4 : rk(P :: R :: Pp :: Qp :: alpha :: nil) >= 4).
{
	assert(HPRPpRpOoalphaeq : rk(P :: R :: Pp :: Rp :: Oo :: alpha :: nil) = 3) by (apply LPRPpRpOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPRPpRpOoalphaMtmp : rk(P :: R :: Pp :: Rp :: Oo :: alpha :: nil) <= 3) by (solve_hyps_max HPRPpRpOoalphaeq HPRPpRpOoalphaM3).
	assert(HPRPpQpRpOoalphaeq : rk(P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: nil) = 4) by (apply LPRPpQpRpOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPRPpQpRpOoalphamtmp : rk(P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: nil) >= 4) by (solve_hyps_min HPRPpQpRpOoalphaeq HPRPpQpRpOoalpham4).
	assert(HPRPpalphaeq : rk(P :: R :: Pp :: alpha :: nil) = 3) by (apply LPRPpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPRPpalphamtmp : rk(P :: R :: Pp :: alpha :: nil) >= 3) by (solve_hyps_min HPRPpalphaeq HPRPpalpham3).
	assert(Hincl : incl (P :: R :: Pp :: alpha :: nil) (list_inter (P :: R :: Pp :: Qp :: alpha :: nil) (P :: R :: Pp :: Rp :: Oo :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: nil) (P :: R :: Pp :: Qp :: alpha :: P :: R :: Pp :: Rp :: Oo :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: Pp :: Qp :: alpha :: P :: R :: Pp :: Rp :: Oo :: alpha :: nil) ((P :: R :: Pp :: Qp :: alpha :: nil) ++ (P :: R :: Pp :: Rp :: Oo :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPRPpQpRpOoalphamtmp;try rewrite HT2 in HPRPpQpRpOoalphamtmp.
	assert(HT := rule_2 (P :: R :: Pp :: Qp :: alpha :: nil) (P :: R :: Pp :: Rp :: Oo :: alpha :: nil) (P :: R :: Pp :: alpha :: nil) 4 3 3 HPRPpQpRpOoalphamtmp HPRPpalphamtmp HPRPpRpOoalphaMtmp Hincl);apply HT.
}

assert(HPRPpQpalphaM : rk(P :: R :: Pp :: Qp :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPRPpQpalpham : rk(P :: R :: Pp :: Qp :: alpha ::  nil) >= 1) by (solve_hyps_min HPRPpQpalphaeq HPRPpQpalpham1).
intuition.
Qed.

(* dans constructLemma(), requis par LPQRPpQpalpha *)
(* dans la couche 0 *)
Lemma LPQRPpQpOoalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQpOoalpha requis par la preuve de (?)PQRPpQpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpm2 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -1 et -2*)
assert(HPQRPpQpm3 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3).
{
	assert(HRpMtmp : rk(Rp :: nil) <= 1) by (solve_hyps_max HRpeq HRpM1).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) ((P :: Q :: R :: Pp :: Qp :: nil) ++ (Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_2 (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil) (nil) 4 0 1 HPQRPpQpRpmtmp Hmtmp HRpMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQpOoalpha requis par la preuve de (?)PQRPpQpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQpOoalpha requis par la preuve de (?)PQRPpQpOoalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpOoalpham2 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPQRPpQpOoalpham3 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) >= 3).
{
	assert(HPQRPpQpmtmp : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3) by (solve_hyps_min HPQRPpQpeq HPQRPpQpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) 3 3 HPQRPpQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpOoalpham4 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

assert(HPQRPpQpOoalphaM : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRPpQpOoalpham : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha ::  nil) >= 1) by (solve_hyps_min HPQRPpQpOoalphaeq HPQRPpQpOoalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPQRPpQpalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: alpha ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQpalpha requis par la preuve de (?)PQRPpQpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQpalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpm2 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -1 et -2*)
assert(HPQRPpQpm3 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3).
{
	assert(HRpMtmp : rk(Rp :: nil) <= 1) by (solve_hyps_max HRpeq HRpM1).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) ((P :: Q :: R :: Pp :: Qp :: nil) ++ (Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_2 (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil) (nil) 4 0 1 HPQRPpQpRpmtmp Hmtmp HRpMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQpalpha requis par la preuve de (?)PQRPpQpalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQpalpha requis par la preuve de (?)PQRPpQpalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpalpham2 : rk(P :: Q :: R :: Pp :: Qp :: alpha :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: alpha :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPQRPpQpalpham3 : rk(P :: Q :: R :: Pp :: Qp :: alpha :: nil) >= 3).
{
	assert(HPQRPpQpmtmp : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3) by (solve_hyps_min HPQRPpQpeq HPQRPpQpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: alpha :: nil) 3 3 HPQRPpQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 -4 et -4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Oo :: alpha ::  de rang :  4 et 4 	 AiB : P :: Pp ::  de rang :  2 et 2 	 A : P :: Pp :: Oo ::   de rang : 2 et 2 *)
assert(HPQRPpQpalpham4 : rk(P :: Q :: R :: Pp :: Qp :: alpha :: nil) >= 4).
{
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	assert(HPQRPpQpOoalphaeq : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) = 4) by (apply LPQRPpQpOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQRPpQpOoalphamtmp : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) >= 4) by (solve_hyps_min HPQRPpQpOoalphaeq HPQRPpQpOoalpham4).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hincl : incl (P :: Pp :: nil) (list_inter (P :: Pp :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: nil) (P :: Pp :: Oo :: P :: Q :: R :: Pp :: Qp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Oo :: P :: Q :: R :: Pp :: Qp :: alpha :: nil) ((P :: Pp :: Oo :: nil) ++ (P :: Q :: R :: Pp :: Qp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpOoalphamtmp;try rewrite HT2 in HPQRPpQpOoalphamtmp.
	assert(HT := rule_4 (P :: Pp :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: alpha :: nil) (P :: Pp :: nil) 4 2 2 HPQRPpQpOoalphamtmp HPPpmtmp HPPpOoMtmp Hincl); apply HT.
}

assert(HPQRPpQpalphaM : rk(P :: Q :: R :: Pp :: Qp :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRPpQpalpham : rk(P :: Q :: R :: Pp :: Qp :: alpha ::  nil) >= 1) by (solve_hyps_min HPQRPpQpalphaeq HPQRPpQpalpham1).
intuition.
Qed.

(* dans constructLemma(), requis par LRpalpha *)
(* dans constructLemma(), requis par LPRRpalpha *)
(* dans la couche 0 *)
Lemma LPRRpOoalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: R :: Rp :: Oo :: alpha ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRRpOoalpha requis par la preuve de (?)PRRpOoalpha pour la règle 1  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour PQRQpRpOoalpha requis par la preuve de (?)PRRpOoalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRQpRpOoalpha requis par la preuve de (?)PQRQpRpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRQpRp requis par la preuve de (?)PQRQpRpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRQpRp requis par la preuve de (?)PQRQpRp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: -4 -2 et -4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Rp ::  de rang :  4 et 4 	 AiB : P ::  de rang :  1 et 1 	 A : P :: Pp ::   de rang : 2 et 2 *)
assert(HPQRQpRpm3 : rk(P :: Q :: R :: Qp :: Rp :: nil) >= 3).
{
	assert(HPPpMtmp : rk(P :: Pp :: nil) <= 2) by (solve_hyps_max HPPpeq HPPpM2).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(HPmtmp : rk(P :: nil) >= 1) by (solve_hyps_min HPeq HPm1).
	assert(Hincl : incl (P :: nil) (list_inter (P :: Pp :: nil) (P :: Q :: R :: Qp :: Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Pp :: P :: Q :: R :: Qp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: P :: Q :: R :: Qp :: Rp :: nil) ((P :: Pp :: nil) ++ (P :: Q :: R :: Qp :: Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_4 (P :: Pp :: nil) (P :: Q :: R :: Qp :: Rp :: nil) (P :: nil) 4 1 2 HPQRPpQpRpmtmp HPmtmp HPPpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRQpRpOoalpha requis par la preuve de (?)PQRQpRpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRQpRpOoalpha requis par la preuve de (?)PQRQpRpOoalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRQpRpOoalpham2 : rk(P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: nil) >= 2).
{
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Q :: Qp :: nil) (P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: Qp :: nil) (P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: nil) 2 2 HQQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPQRQpRpOoalpham3 : rk(P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: nil) >= 3).
{
	assert(HPQRQpRpmtmp : rk(P :: Q :: R :: Qp :: Rp :: nil) >= 3) by (solve_hyps_min HPQRQpRpeq HPQRQpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Qp :: Rp :: nil) (P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Qp :: Rp :: nil) (P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: nil) 3 3 HPQRQpRpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRQpRpOoalpham4 : rk(P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRRpOoalpha requis par la preuve de (?)PRRpOoalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRRpOoalpha requis par la preuve de (?)PRRpOoalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPRRpOoalpham2 : rk(P :: R :: Rp :: Oo :: alpha :: nil) >= 2).
{
	assert(HRRpmtmp : rk(R :: Rp :: nil) >= 2) by (solve_hyps_min HRRpeq HRRpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (R :: Rp :: nil) (P :: R :: Rp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (R :: Rp :: nil) (P :: R :: Rp :: Oo :: alpha :: nil) 2 2 HRRpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : P :: Q :: R :: Qp :: Rp :: Oo :: alpha ::  de rang :  4 et 4 	 AiB : Oo ::  de rang :  1 et 1 	 A : Q :: Qp :: Oo ::   de rang : 2 et 2 *)
assert(HPRRpOoalpham3 : rk(P :: R :: Rp :: Oo :: alpha :: nil) >= 3).
{
	assert(HQQpOoMtmp : rk(Q :: Qp :: Oo :: nil) <= 2) by (solve_hyps_max HQQpOoeq HQQpOoM2).
	assert(HPQRQpRpOoalphamtmp : rk(P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: nil) >= 4) by (solve_hyps_min HPQRQpRpOoalphaeq HPQRQpRpOoalpham4).
	assert(HOomtmp : rk(Oo :: nil) >= 1) by (solve_hyps_min HOoeq HOom1).
	assert(Hincl : incl (Oo :: nil) (list_inter (Q :: Qp :: Oo :: nil) (P :: R :: Rp :: Oo :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: nil) (Q :: Qp :: Oo :: P :: R :: Rp :: Oo :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Qp :: Oo :: P :: R :: Rp :: Oo :: alpha :: nil) ((Q :: Qp :: Oo :: nil) ++ (P :: R :: Rp :: Oo :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRQpRpOoalphamtmp;try rewrite HT2 in HPQRQpRpOoalphamtmp.
	assert(HT := rule_4 (Q :: Qp :: Oo :: nil) (P :: R :: Rp :: Oo :: alpha :: nil) (Oo :: nil) 4 1 2 HPQRQpRpOoalphamtmp HOomtmp HQQpOoMtmp Hincl); apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -2*)
assert(HPRRpOoalphaM3 : rk(P :: R :: Rp :: Oo :: alpha :: nil) <= 3).
{
	assert(HRRpOoMtmp : rk(R :: Rp :: Oo :: nil) <= 2) by (solve_hyps_max HRRpOoeq HRRpOoM2).
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	assert(HRmtmp : rk(R :: nil) >= 1) by (solve_hyps_min HReq HRm1).
	assert(Hincl : incl (R :: nil) (list_inter (R :: Rp :: Oo :: nil) (P :: R :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Rp :: Oo :: alpha :: nil) (R :: Rp :: Oo :: P :: R :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (R :: Rp :: Oo :: P :: R :: alpha :: nil) ((R :: Rp :: Oo :: nil) ++ (P :: R :: alpha :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (R :: Rp :: Oo :: nil) (P :: R :: alpha :: nil) (R :: nil) 2 2 1 HRRpOoMtmp HPRalphaMtmp HRmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HPRRpOoalphaM : rk(P :: R :: Rp :: Oo :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPRRpOoalpham : rk(P :: R :: Rp :: Oo :: alpha ::  nil) >= 1) by (solve_hyps_min HPRRpOoalphaeq HPRRpOoalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPRRpalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: R :: Rp :: alpha ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PRRpalpha requis par la preuve de (?)PRRpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour PRRpalpha requis par la preuve de (?)PRRpalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRRpalpha requis par la preuve de (?)PRRpalpha pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HPRRpalphaM3 : rk(P :: R :: Rp :: alpha :: nil) <= 3).
{
	assert(HRpMtmp : rk(Rp :: nil) <= 1) by (solve_hyps_max HRpeq HRpM1).
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Rp :: nil) (P :: R :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Rp :: alpha :: nil) (Rp :: P :: R :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Rp :: P :: R :: alpha :: nil) ((Rp :: nil) ++ (P :: R :: alpha :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Rp :: nil) (P :: R :: alpha :: nil) (nil) 1 2 0 HRpMtmp HPRalphaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPRRpalpham2 : rk(P :: R :: Rp :: alpha :: nil) >= 2).
{
	assert(HRRpmtmp : rk(R :: Rp :: nil) >= 2) by (solve_hyps_min HRRpeq HRRpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (R :: Rp :: nil) (P :: R :: Rp :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (R :: Rp :: nil) (P :: R :: Rp :: alpha :: nil) 2 2 HRRpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 -4 et -4*)
(* ensembles concernés AUB : P :: R :: Rp :: Oo :: alpha ::  de rang :  3 et 3 	 AiB : R :: Rp ::  de rang :  2 et 2 	 A : R :: Rp :: Oo ::   de rang : 2 et 2 *)
assert(HPRRpalpham3 : rk(P :: R :: Rp :: alpha :: nil) >= 3).
{
	assert(HRRpOoMtmp : rk(R :: Rp :: Oo :: nil) <= 2) by (solve_hyps_max HRRpOoeq HRRpOoM2).
	assert(HPRRpOoalphaeq : rk(P :: R :: Rp :: Oo :: alpha :: nil) = 3) by (apply LPRRpOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPRRpOoalphamtmp : rk(P :: R :: Rp :: Oo :: alpha :: nil) >= 3) by (solve_hyps_min HPRRpOoalphaeq HPRRpOoalpham3).
	assert(HRRpmtmp : rk(R :: Rp :: nil) >= 2) by (solve_hyps_min HRRpeq HRRpm2).
	assert(Hincl : incl (R :: Rp :: nil) (list_inter (R :: Rp :: Oo :: nil) (P :: R :: Rp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Rp :: Oo :: alpha :: nil) (R :: Rp :: Oo :: P :: R :: Rp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (R :: Rp :: Oo :: P :: R :: Rp :: alpha :: nil) ((R :: Rp :: Oo :: nil) ++ (P :: R :: Rp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPRRpOoalphamtmp;try rewrite HT2 in HPRRpOoalphamtmp.
	assert(HT := rule_4 (R :: Rp :: Oo :: nil) (P :: R :: Rp :: alpha :: nil) (R :: Rp :: nil) 3 2 2 HPRRpOoalphamtmp HRRpmtmp HRRpOoMtmp Hincl); apply HT.
}

assert(HPRRpalphaM : rk(P :: R :: Rp :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPRRpalpham : rk(P :: R :: Rp :: alpha ::  nil) >= 1) by (solve_hyps_min HPRRpalphaeq HPRRpalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LRpalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(Rp :: alpha ::  nil) = 2.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour Rpalpha requis par la preuve de (?)Rpalpha pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 2) *)
(* marque des antécédents AUB AiB A: 4 -2 et -4*)
(* ensembles concernés AUB : P :: R :: Rp :: alpha ::  de rang :  3 et 3 	 AiB : alpha ::  de rang :  1 et 1 	 A : P :: R :: alpha ::   de rang : 2 et 2 *)
assert(HRpalpham2 : rk(Rp :: alpha :: nil) >= 2).
{
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	assert(HPRRpalphaeq : rk(P :: R :: Rp :: alpha :: nil) = 3) by (apply LPRRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPRRpalphamtmp : rk(P :: R :: Rp :: alpha :: nil) >= 3) by (solve_hyps_min HPRRpalphaeq HPRRpalpham3).
	assert(Halphamtmp : rk(alpha :: nil) >= 1) by (solve_hyps_min Halphaeq Halpham1).
	assert(Hincl : incl (alpha :: nil) (list_inter (P :: R :: alpha :: nil) (Rp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Rp :: alpha :: nil) (P :: R :: alpha :: Rp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: alpha :: Rp :: alpha :: nil) ((P :: R :: alpha :: nil) ++ (Rp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPRRpalphamtmp;try rewrite HT2 in HPRRpalphamtmp.
	assert(HT := rule_4 (P :: R :: alpha :: nil) (Rp :: alpha :: nil) (alpha :: nil) 3 1 2 HPRRpalphamtmp Halphamtmp HPRalphaMtmp Hincl); apply HT.
}

assert(HRpalphaM : rk(Rp :: alpha ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HRpalphaeq HRpalphaM2).
assert(HRpalpham : rk(Rp :: alpha ::  nil) >= 1) by (solve_hyps_min HRpalphaeq HRpalpham1).
intuition.
Qed.

(* dans constructLemma(), requis par LPPpRpalpha *)
(* dans la couche 0 *)
Lemma LPPpQpRpOoalphabeta : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PPpQpRpOoalphabeta requis par la preuve de (?)PPpQpRpOoalphabeta pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PPpQpRpOoalphabeta requis par la preuve de (?)PPpQpRpOoalphabeta pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPPpQpRpOoalphabetam2 : rk(P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPPpQpRpOoalphabetam4 : rk(P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: nil) >= 4).
{
	assert(HPpQpRpOomtmp : rk(Pp :: Qp :: Rp :: Oo :: nil) >= 4) by (solve_hyps_min HPpQpRpOoeq HPpQpRpOom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: Rp :: Oo :: nil) (P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: Rp :: Oo :: nil) (P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: nil) 4 4 HPpQpRpOomtmp Hcomp Hincl);apply HT.
}

assert(HPPpQpRpOoalphabetaM : rk(P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPPpQpRpOoalphabetam : rk(P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta ::  nil) >= 1) by (solve_hyps_min HPPpQpRpOoalphabetaeq HPPpQpRpOoalphabetam1).
intuition.
Qed.

(* dans constructLemma(), requis par LPPpRpalpha *)
(* dans la couche 0 *)
Lemma LPPpQpOobeta : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Pp :: Qp :: Oo :: beta ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PPpQpOobeta requis par la preuve de (?)PPpQpOobeta pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PPpQpOobeta requis par la preuve de (?)PPpQpOobeta pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PPpQpOobeta requis par la preuve de (?)PPpQpOobeta pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPPpQpOobetam2 : rk(P :: Pp :: Qp :: Oo :: beta :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Pp :: Qp :: Oo :: beta :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Pp :: Qp :: Oo :: beta :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -2*)
assert(HPPpQpOobetaM3 : rk(P :: Pp :: Qp :: Oo :: beta :: nil) <= 3).
{
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	assert(HPpQpbetaMtmp : rk(Pp :: Qp :: beta :: nil) <= 2) by (solve_hyps_max HPpQpbetaeq HPpQpbetaM2).
	assert(HPpmtmp : rk(Pp :: nil) >= 1) by (solve_hyps_min HPpeq HPpm1).
	assert(Hincl : incl (Pp :: nil) (list_inter (P :: Pp :: Oo :: nil) (Pp :: Qp :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Pp :: Qp :: Oo :: beta :: nil) (P :: Pp :: Oo :: Pp :: Qp :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Oo :: Pp :: Qp :: beta :: nil) ((P :: Pp :: Oo :: nil) ++ (Pp :: Qp :: beta :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P :: Pp :: Oo :: nil) (Pp :: Qp :: beta :: nil) (Pp :: nil) 2 2 1 HPPpOoMtmp HPpQpbetaMtmp HPpmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 -2 et -4*)
(* ensembles concernés AUB : P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta ::  de rang :  4 et 4 	 AiB : Pp ::  de rang :  1 et 1 	 A : Pp :: Rp :: alpha ::   de rang : 2 et 2 *)
assert(HPPpQpOobetam3 : rk(P :: Pp :: Qp :: Oo :: beta :: nil) >= 3).
{
	assert(HPpRpalphaMtmp : rk(Pp :: Rp :: alpha :: nil) <= 2) by (solve_hyps_max HPpRpalphaeq HPpRpalphaM2).
	assert(HPPpQpRpOoalphabetaeq : rk(P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: nil) = 4) by (apply LPPpQpRpOoalphabeta with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPPpQpRpOoalphabetamtmp : rk(P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: nil) >= 4) by (solve_hyps_min HPPpQpRpOoalphabetaeq HPPpQpRpOoalphabetam4).
	assert(HPpmtmp : rk(Pp :: nil) >= 1) by (solve_hyps_min HPpeq HPpm1).
	assert(Hincl : incl (Pp :: nil) (list_inter (Pp :: Rp :: alpha :: nil) (P :: Pp :: Qp :: Oo :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: nil) (Pp :: Rp :: alpha :: P :: Pp :: Qp :: Oo :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: Rp :: alpha :: P :: Pp :: Qp :: Oo :: beta :: nil) ((Pp :: Rp :: alpha :: nil) ++ (P :: Pp :: Qp :: Oo :: beta :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPPpQpRpOoalphabetamtmp;try rewrite HT2 in HPPpQpRpOoalphabetamtmp.
	assert(HT := rule_4 (Pp :: Rp :: alpha :: nil) (P :: Pp :: Qp :: Oo :: beta :: nil) (Pp :: nil) 4 1 2 HPPpQpRpOoalphabetamtmp HPpmtmp HPpRpalphaMtmp Hincl); apply HT.
}

assert(HPPpQpOobetaM : rk(P :: Pp :: Qp :: Oo :: beta ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPPpQpOobetam : rk(P :: Pp :: Qp :: Oo :: beta ::  nil) >= 1) by (solve_hyps_min HPPpQpOobetaeq HPPpQpOobetam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPPpRpalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Pp :: Rp :: alpha ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PPpRpalpha requis par la preuve de (?)PPpRpalpha pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour PPpRpalpha requis par la preuve de (?)PPpRpalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PPpRpalpha requis par la preuve de (?)PPpRpalpha pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HPPpRpalphaM3 : rk(P :: Pp :: Rp :: alpha :: nil) <= 3).
{
	assert(HPMtmp : rk(P :: nil) <= 1) by (solve_hyps_max HPeq HPM1).
	assert(HPpRpalphaMtmp : rk(Pp :: Rp :: alpha :: nil) <= 2) by (solve_hyps_max HPpRpalphaeq HPpRpalphaM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P :: nil) (Pp :: Rp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Pp :: Rp :: alpha :: nil) (P :: Pp :: Rp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Rp :: alpha :: nil) ((P :: nil) ++ (Pp :: Rp :: alpha :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P :: nil) (Pp :: Rp :: alpha :: nil) (nil) 1 2 0 HPMtmp HPpRpalphaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPPpRpalpham2 : rk(P :: Pp :: Rp :: alpha :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Pp :: Rp :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Pp :: Rp :: alpha :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -4 et 4*)
assert(HPPpRpalpham3 : rk(P :: Pp :: Rp :: alpha :: nil) >= 3).
{
	assert(HPPpQpOobetaeq : rk(P :: Pp :: Qp :: Oo :: beta :: nil) = 3) by (apply LPPpQpOobeta with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPPpQpOobetaMtmp : rk(P :: Pp :: Qp :: Oo :: beta :: nil) <= 3) by (solve_hyps_max HPPpQpOobetaeq HPPpQpOobetaM3).
	assert(HPPpQpRpOoalphabetaeq : rk(P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: nil) = 4) by (apply LPPpQpRpOoalphabeta with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPPpQpRpOoalphabetamtmp : rk(P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: nil) >= 4) by (solve_hyps_min HPPpQpRpOoalphabetaeq HPPpQpRpOoalphabetam4).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hincl : incl (P :: Pp :: nil) (list_inter (P :: Pp :: Rp :: alpha :: nil) (P :: Pp :: Qp :: Oo :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: nil) (P :: Pp :: Rp :: alpha :: P :: Pp :: Qp :: Oo :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Rp :: alpha :: P :: Pp :: Qp :: Oo :: beta :: nil) ((P :: Pp :: Rp :: alpha :: nil) ++ (P :: Pp :: Qp :: Oo :: beta :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPPpQpRpOoalphabetamtmp;try rewrite HT2 in HPPpQpRpOoalphabetamtmp.
	assert(HT := rule_2 (P :: Pp :: Rp :: alpha :: nil) (P :: Pp :: Qp :: Oo :: beta :: nil) (P :: Pp :: nil) 4 2 3 HPPpQpRpOoalphabetamtmp HPPpmtmp HPPpQpOobetaMtmp Hincl);apply HT.
}

assert(HPPpRpalphaM : rk(P :: Pp :: Rp :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPPpRpalpham : rk(P :: Pp :: Rp :: alpha ::  nil) >= 1) by (solve_hyps_min HPPpRpalphaeq HPPpRpalpham1).
intuition.
Qed.

(* dans constructLemma(), requis par LPQPpRpalpha *)
(* dans constructLemma(), requis par LPQRPpRpalpha *)
(* dans la couche 0 *)
Lemma LPQRPpRpOoalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Rp :: Oo :: alpha ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpRpOoalpha requis par la preuve de (?)PQRPpRpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpRp requis par la preuve de (?)PQRPpRpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpRp requis par la preuve de (?)PQRPpRp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpRp requis par la preuve de (?)PQRPpRp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpRpm2 : rk(P :: Q :: R :: Pp :: Rp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Rp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Rp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: -4 -1 et -2*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Rp ::  de rang :  4 et 4 	 AiB :  de rang :  0 et 0 	 A : Qp ::   de rang : 1 et 1 *)
assert(HPQRPpRpm3 : rk(P :: Q :: R :: Pp :: Rp :: nil) >= 3).
{
	assert(HQpMtmp : rk(Qp :: nil) <= 1) by (solve_hyps_max HQpeq HQpM1).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Qp :: nil) (P :: Q :: R :: Pp :: Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (Qp :: P :: Q :: R :: Pp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Qp :: P :: Q :: R :: Pp :: Rp :: nil) ((Qp :: nil) ++ (P :: Q :: R :: Pp :: Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_4 (Qp :: nil) (P :: Q :: R :: Pp :: Rp :: nil) (nil) 4 0 1 HPQRPpQpRpmtmp Hmtmp HQpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpRpOoalpha requis par la preuve de (?)PQRPpRpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpRpOoalpha requis par la preuve de (?)PQRPpRpOoalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpRpOoalpham2 : rk(P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPQRPpRpOoalpham3 : rk(P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil) >= 3).
{
	assert(HPQRPpRpmtmp : rk(P :: Q :: R :: Pp :: Rp :: nil) >= 3) by (solve_hyps_min HPQRPpRpeq HPQRPpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Pp :: Rp :: nil) (P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Pp :: Rp :: nil) (P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil) 3 3 HPQRPpRpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpRpOoalpham4 : rk(P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

assert(HPQRPpRpOoalphaM : rk(P :: Q :: R :: Pp :: Rp :: Oo :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRPpRpOoalpham : rk(P :: Q :: R :: Pp :: Rp :: Oo :: alpha ::  nil) >= 1) by (solve_hyps_min HPQRPpRpOoalphaeq HPQRPpRpOoalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPQRPpRpalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Rp :: alpha ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpRpalpha requis par la preuve de (?)PQRPpRpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpRp requis par la preuve de (?)PQRPpRpalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpRp requis par la preuve de (?)PQRPpRp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpRp requis par la preuve de (?)PQRPpRp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpRpm2 : rk(P :: Q :: R :: Pp :: Rp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Rp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Rp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: -4 -1 et -2*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Rp ::  de rang :  4 et 4 	 AiB :  de rang :  0 et 0 	 A : Qp ::   de rang : 1 et 1 *)
assert(HPQRPpRpm3 : rk(P :: Q :: R :: Pp :: Rp :: nil) >= 3).
{
	assert(HQpMtmp : rk(Qp :: nil) <= 1) by (solve_hyps_max HQpeq HQpM1).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Qp :: nil) (P :: Q :: R :: Pp :: Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (Qp :: P :: Q :: R :: Pp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Qp :: P :: Q :: R :: Pp :: Rp :: nil) ((Qp :: nil) ++ (P :: Q :: R :: Pp :: Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_4 (Qp :: nil) (P :: Q :: R :: Pp :: Rp :: nil) (nil) 4 0 1 HPQRPpQpRpmtmp Hmtmp HQpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpRpalpha requis par la preuve de (?)PQRPpRpalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpRpalpha requis par la preuve de (?)PQRPpRpalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpRpalpham2 : rk(P :: Q :: R :: Pp :: Rp :: alpha :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Rp :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Rp :: alpha :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPQRPpRpalpham3 : rk(P :: Q :: R :: Pp :: Rp :: alpha :: nil) >= 3).
{
	assert(HPQRPpRpmtmp : rk(P :: Q :: R :: Pp :: Rp :: nil) >= 3) by (solve_hyps_min HPQRPpRpeq HPQRPpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Pp :: Rp :: nil) (P :: Q :: R :: Pp :: Rp :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Pp :: Rp :: nil) (P :: Q :: R :: Pp :: Rp :: alpha :: nil) 3 3 HPQRPpRpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 -4 et -4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Rp :: Oo :: alpha ::  de rang :  4 et 4 	 AiB : P :: Pp ::  de rang :  2 et 2 	 A : P :: Pp :: Oo ::   de rang : 2 et 2 *)
assert(HPQRPpRpalpham4 : rk(P :: Q :: R :: Pp :: Rp :: alpha :: nil) >= 4).
{
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	assert(HPQRPpRpOoalphaeq : rk(P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil) = 4) by (apply LPQRPpRpOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQRPpRpOoalphamtmp : rk(P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil) >= 4) by (solve_hyps_min HPQRPpRpOoalphaeq HPQRPpRpOoalpham4).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hincl : incl (P :: Pp :: nil) (list_inter (P :: Pp :: Oo :: nil) (P :: Q :: R :: Pp :: Rp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil) (P :: Pp :: Oo :: P :: Q :: R :: Pp :: Rp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Oo :: P :: Q :: R :: Pp :: Rp :: alpha :: nil) ((P :: Pp :: Oo :: nil) ++ (P :: Q :: R :: Pp :: Rp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpRpOoalphamtmp;try rewrite HT2 in HPQRPpRpOoalphamtmp.
	assert(HT := rule_4 (P :: Pp :: Oo :: nil) (P :: Q :: R :: Pp :: Rp :: alpha :: nil) (P :: Pp :: nil) 4 2 2 HPQRPpRpOoalphamtmp HPPpmtmp HPPpOoMtmp Hincl); apply HT.
}

assert(HPQRPpRpalphaM : rk(P :: Q :: R :: Pp :: Rp :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRPpRpalpham : rk(P :: Q :: R :: Pp :: Rp :: alpha ::  nil) >= 1) by (solve_hyps_min HPQRPpRpalphaeq HPQRPpRpalpham1).
intuition.
Qed.

(* dans constructLemma(), requis par LPQPpRpalpha *)
(* dans la couche 0 *)
Lemma LPRPpRpalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: R :: Pp :: Rp :: alpha ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRPpRpalpha requis par la preuve de (?)PRPpRpalpha pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpRpalpha requis par la preuve de (?)PRPpRpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpRpalpha requis par la preuve de (?)PRPpRpalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPRPpRpalpham2 : rk(P :: R :: Pp :: Rp :: alpha :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Rp :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Rp :: alpha :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 4 -4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Rp :: Oo :: alpha ::  de rang :  4 et 4 	 AiB : P :: Pp ::  de rang :  2 et 2 	 A : P :: Q :: Pp :: Oo ::   de rang : 3 et 3 *)
assert(HPRPpRpalpham3 : rk(P :: R :: Pp :: Rp :: alpha :: nil) >= 3).
{
	assert(HPQPpOoeq : rk(P :: Q :: Pp :: Oo :: nil) = 3) by (apply LPQPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQPpOoMtmp : rk(P :: Q :: Pp :: Oo :: nil) <= 3) by (solve_hyps_max HPQPpOoeq HPQPpOoM3).
	assert(HPQRPpRpOoalphaeq : rk(P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil) = 4) by (apply LPQRPpRpOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQRPpRpOoalphamtmp : rk(P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil) >= 4) by (solve_hyps_min HPQRPpRpOoalphaeq HPQRPpRpOoalpham4).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hincl : incl (P :: Pp :: nil) (list_inter (P :: Q :: Pp :: Oo :: nil) (P :: R :: Pp :: Rp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil) (P :: Q :: Pp :: Oo :: P :: R :: Pp :: Rp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: Pp :: Oo :: P :: R :: Pp :: Rp :: alpha :: nil) ((P :: Q :: Pp :: Oo :: nil) ++ (P :: R :: Pp :: Rp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpRpOoalphamtmp;try rewrite HT2 in HPQRPpRpOoalphamtmp.
	assert(HT := rule_4 (P :: Q :: Pp :: Oo :: nil) (P :: R :: Pp :: Rp :: alpha :: nil) (P :: Pp :: nil) 4 2 3 HPQRPpRpOoalphamtmp HPPpmtmp HPQPpOoMtmp Hincl); apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -2*)
assert(HPRPpRpalphaM3 : rk(P :: R :: Pp :: Rp :: alpha :: nil) <= 3).
{
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	assert(HPpRpalphaMtmp : rk(Pp :: Rp :: alpha :: nil) <= 2) by (solve_hyps_max HPpRpalphaeq HPpRpalphaM2).
	assert(Halphamtmp : rk(alpha :: nil) >= 1) by (solve_hyps_min Halphaeq Halpham1).
	assert(Hincl : incl (alpha :: nil) (list_inter (P :: R :: alpha :: nil) (Pp :: Rp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: Rp :: alpha :: nil) (P :: R :: alpha :: Pp :: Rp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: alpha :: Pp :: Rp :: alpha :: nil) ((P :: R :: alpha :: nil) ++ (Pp :: Rp :: alpha :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P :: R :: alpha :: nil) (Pp :: Rp :: alpha :: nil) (alpha :: nil) 2 2 1 HPRalphaMtmp HPpRpalphaMtmp Halphamtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HPRPpRpalphaM : rk(P :: R :: Pp :: Rp :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPRPpRpalpham : rk(P :: R :: Pp :: Rp :: alpha ::  nil) >= 1) by (solve_hyps_min HPRPpRpalphaeq HPRPpRpalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPQPpRpalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Q :: Pp :: Rp :: alpha ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQPpRpalpha requis par la preuve de (?)PQPpRpalpha pour la règle 2  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQPpRpalpha requis par la preuve de (?)PQPpRpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQPpRpalpha requis par la preuve de (?)PQPpRpalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQPpRpalpham2 : rk(P :: Q :: Pp :: Rp :: alpha :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: Pp :: Rp :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: Pp :: Rp :: alpha :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 4 -4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Rp :: Oo :: alpha ::  de rang :  4 et 4 	 AiB : P :: Pp ::  de rang :  2 et 2 	 A : P :: R :: Pp :: Oo ::   de rang : 3 et 3 *)
assert(HPQPpRpalpham3 : rk(P :: Q :: Pp :: Rp :: alpha :: nil) >= 3).
{
	assert(HPRPpOoeq : rk(P :: R :: Pp :: Oo :: nil) = 3) by (apply LPRPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPRPpOoMtmp : rk(P :: R :: Pp :: Oo :: nil) <= 3) by (solve_hyps_max HPRPpOoeq HPRPpOoM3).
	assert(HPQRPpRpOoalphaeq : rk(P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil) = 4) by (apply LPQRPpRpOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQRPpRpOoalphamtmp : rk(P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil) >= 4) by (solve_hyps_min HPQRPpRpOoalphaeq HPQRPpRpOoalpham4).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hincl : incl (P :: Pp :: nil) (list_inter (P :: R :: Pp :: Oo :: nil) (P :: Q :: Pp :: Rp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Rp :: Oo :: alpha :: nil) (P :: R :: Pp :: Oo :: P :: Q :: Pp :: Rp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: Pp :: Oo :: P :: Q :: Pp :: Rp :: alpha :: nil) ((P :: R :: Pp :: Oo :: nil) ++ (P :: Q :: Pp :: Rp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpRpOoalphamtmp;try rewrite HT2 in HPQRPpRpOoalphamtmp.
	assert(HT := rule_4 (P :: R :: Pp :: Oo :: nil) (P :: Q :: Pp :: Rp :: alpha :: nil) (P :: Pp :: nil) 4 2 3 HPQRPpRpOoalphamtmp HPPpmtmp HPRPpOoMtmp Hincl); apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 4*)
assert(HPQPpRpalpham4 : rk(P :: Q :: Pp :: Rp :: alpha :: nil) >= 4).
{
	assert(HPRPpRpalphaeq : rk(P :: R :: Pp :: Rp :: alpha :: nil) = 3) by (apply LPRPpRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPRPpRpalphaMtmp : rk(P :: R :: Pp :: Rp :: alpha :: nil) <= 3) by (solve_hyps_max HPRPpRpalphaeq HPRPpRpalphaM3).
	assert(HPQRPpRpalphaeq : rk(P :: Q :: R :: Pp :: Rp :: alpha :: nil) = 4) by (apply LPQRPpRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQRPpRpalphamtmp : rk(P :: Q :: R :: Pp :: Rp :: alpha :: nil) >= 4) by (solve_hyps_min HPQRPpRpalphaeq HPQRPpRpalpham4).
	assert(HPPpRpalphaeq : rk(P :: Pp :: Rp :: alpha :: nil) = 3) by (apply LPPpRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPPpRpalphamtmp : rk(P :: Pp :: Rp :: alpha :: nil) >= 3) by (solve_hyps_min HPPpRpalphaeq HPPpRpalpham3).
	assert(Hincl : incl (P :: Pp :: Rp :: alpha :: nil) (list_inter (P :: Q :: Pp :: Rp :: alpha :: nil) (P :: R :: Pp :: Rp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Rp :: alpha :: nil) (P :: Q :: Pp :: Rp :: alpha :: P :: R :: Pp :: Rp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: Pp :: Rp :: alpha :: P :: R :: Pp :: Rp :: alpha :: nil) ((P :: Q :: Pp :: Rp :: alpha :: nil) ++ (P :: R :: Pp :: Rp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpRpalphamtmp;try rewrite HT2 in HPQRPpRpalphamtmp.
	assert(HT := rule_2 (P :: Q :: Pp :: Rp :: alpha :: nil) (P :: R :: Pp :: Rp :: alpha :: nil) (P :: Pp :: Rp :: alpha :: nil) 4 3 3 HPQRPpRpalphamtmp HPPpRpalphamtmp HPRPpRpalphaMtmp Hincl);apply HT.
}

assert(HPQPpRpalphaM : rk(P :: Q :: Pp :: Rp :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQPpRpalpham : rk(P :: Q :: Pp :: Rp :: alpha ::  nil) >= 1) by (solve_hyps_min HPQPpRpalphaeq HPQPpRpalpham1).
intuition.
Qed.

(* dans constructLemma(), requis par LPpQpRpalpha *)
(* dans la couche 0 *)
Lemma LPQRPpQpRpalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp :: alpha ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQpRpalpha requis par la preuve de (?)PQRPpQpRpalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQpRpalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpm2 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -1 et -2*)
assert(HPQRPpQpm3 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3).
{
	assert(HRpMtmp : rk(Rp :: nil) <= 1) by (solve_hyps_max HRpeq HRpM1).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) ((P :: Q :: R :: Pp :: Qp :: nil) ++ (Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_2 (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil) (nil) 4 0 1 HPQRPpQpRpmtmp Hmtmp HRpMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQpRpalpha requis par la preuve de (?)PQRPpQpRpalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQpRpalpha requis par la preuve de (?)PQRPpQpRpalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpRpalpham2 : rk(P :: Q :: R :: Pp :: Qp :: Rp :: alpha :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: alpha :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPQRPpQpRpalpham3 : rk(P :: Q :: R :: Pp :: Qp :: Rp :: alpha :: nil) >= 3).
{
	assert(HPQRPpQpmtmp : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3) by (solve_hyps_min HPQRPpQpeq HPQRPpQpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: alpha :: nil) 3 3 HPQRPpQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpRpalpham4 : rk(P :: Q :: R :: Pp :: Qp :: Rp :: alpha :: nil) >= 4).
{
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: alpha :: nil) 4 4 HPQRPpQpRpmtmp Hcomp Hincl);apply HT.
}

assert(HPQRPpQpRpalphaM : rk(P :: Q :: R :: Pp :: Qp :: Rp :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRPpQpRpalpham : rk(P :: Q :: R :: Pp :: Qp :: Rp :: alpha ::  nil) >= 1) by (solve_hyps_min HPQRPpQpRpalphaeq HPQRPpQpRpalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPpQpRpalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(Pp :: Qp :: Rp :: alpha ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PpQpRpalpha requis par la preuve de (?)PpQpRpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRPpQpRpalpha requis par la preuve de (?)PpQpRpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRPpQpRp requis par la preuve de (?)PRPpQpRpalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour QPp requis par la preuve de (?)PRPpQpRp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpQpRp requis par la preuve de (?)PRPpQpRp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpQpRp requis par la preuve de (?)PRPpQpRp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPRPpQpRpm2 : rk(P :: R :: Pp :: Qp :: Rp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: -4 -2 et 5*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Rp ::  de rang :  4 et 4 	 AiB : Pp ::  de rang :  1 et 1 	 A : Q :: Pp ::   de rang : 1 et 2 *)
assert(HPRPpQpRpm3 : rk(P :: R :: Pp :: Qp :: Rp :: nil) >= 3).
{
	assert(HQPpMtmp : rk(Q :: Pp :: nil) <= 2) by (solve_hyps_max HQPpeq HQPpM2).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(HPpmtmp : rk(Pp :: nil) >= 1) by (solve_hyps_min HPpeq HPpm1).
	assert(Hincl : incl (Pp :: nil) (list_inter (Q :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (Q :: Pp :: P :: R :: Pp :: Qp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Pp :: P :: R :: Pp :: Qp :: Rp :: nil) ((Q :: Pp :: nil) ++ (P :: R :: Pp :: Qp :: Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_4 (Q :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: nil) (Pp :: nil) 4 1 2 HPQRPpQpRpmtmp HPpmtmp HQPpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpQpRpalpha requis par la preuve de (?)PRPpQpRpalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpQpRpalpha requis par la preuve de (?)PRPpQpRpalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPRPpQpRpalpham2 : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPRPpQpRpalpham3 : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: nil) >= 3).
{
	assert(HPRPpQpRpmtmp : rk(P :: R :: Pp :: Qp :: Rp :: nil) >= 3) by (solve_hyps_min HPRPpQpRpeq HPRPpQpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: R :: Pp :: Qp :: Rp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: R :: Pp :: Qp :: Rp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: nil) 3 3 HPRPpQpRpmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour PpQpRpalpha requis par la preuve de (?)PpQpRpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PpQpRpalpha requis par la preuve de (?)PpQpRpalpha pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HPpQpRpalphaM3 : rk(Pp :: Qp :: Rp :: alpha :: nil) <= 3).
{
	assert(HQpMtmp : rk(Qp :: nil) <= 1) by (solve_hyps_max HQpeq HQpM1).
	assert(HPpRpalphaMtmp : rk(Pp :: Rp :: alpha :: nil) <= 2) by (solve_hyps_max HPpRpalphaeq HPpRpalphaM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Qp :: nil) (Pp :: Rp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Pp :: Qp :: Rp :: alpha :: nil) (Qp :: Pp :: Rp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Qp :: Pp :: Rp :: alpha :: nil) ((Qp :: nil) ++ (Pp :: Rp :: alpha :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Qp :: nil) (Pp :: Rp :: alpha :: nil) (nil) 1 2 0 HQpMtmp HPpRpalphaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : P :: R :: Pp :: Qp :: Rp :: alpha ::  de rang :  3 et 4 	 AiB : alpha ::  de rang :  1 et 1 	 A : P :: R :: alpha ::   de rang : 2 et 2 *)
assert(HPpQpRpalpham2 : rk(Pp :: Qp :: Rp :: alpha :: nil) >= 2).
{
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	assert(HPRPpQpRpalphamtmp : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: nil) >= 3) by (solve_hyps_min HPRPpQpRpalphaeq HPRPpQpRpalpham3).
	assert(Halphamtmp : rk(alpha :: nil) >= 1) by (solve_hyps_min Halphaeq Halpham1).
	assert(Hincl : incl (alpha :: nil) (list_inter (P :: R :: alpha :: nil) (Pp :: Qp :: Rp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: Qp :: Rp :: alpha :: nil) (P :: R :: alpha :: Pp :: Qp :: Rp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: alpha :: Pp :: Qp :: Rp :: alpha :: nil) ((P :: R :: alpha :: nil) ++ (Pp :: Qp :: Rp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPRPpQpRpalphamtmp;try rewrite HT2 in HPRPpQpRpalphamtmp.
	assert(HT := rule_4 (P :: R :: alpha :: nil) (Pp :: Qp :: Rp :: alpha :: nil) (alpha :: nil) 3 1 2 HPRPpQpRpalphamtmp Halphamtmp HPRalphaMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Rp :: alpha ::  de rang :  4 et 4 	 AiB : Pp :: Qp :: alpha ::  de rang :  3 et 3 	 A : P :: Q :: R :: Pp :: Qp :: alpha ::   de rang : 4 et 4 *)
assert(HPpQpRpalpham3 : rk(Pp :: Qp :: Rp :: alpha :: nil) >= 3).
{
	assert(HPQRPpQpalphaeq : rk(P :: Q :: R :: Pp :: Qp :: alpha :: nil) = 4) by (apply LPQRPpQpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQRPpQpalphaMtmp : rk(P :: Q :: R :: Pp :: Qp :: alpha :: nil) <= 4) by (solve_hyps_max HPQRPpQpalphaeq HPQRPpQpalphaM4).
	assert(HPQRPpQpRpalphaeq : rk(P :: Q :: R :: Pp :: Qp :: Rp :: alpha :: nil) = 4) by (apply LPQRPpQpRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQRPpQpRpalphamtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: alpha :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpalphaeq HPQRPpQpRpalpham4).
	assert(HPpQpalphaeq : rk(Pp :: Qp :: alpha :: nil) = 3) by (apply LPpQpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpQpalphamtmp : rk(Pp :: Qp :: alpha :: nil) >= 3) by (solve_hyps_min HPpQpalphaeq HPpQpalpham3).
	assert(Hincl : incl (Pp :: Qp :: alpha :: nil) (list_inter (P :: Q :: R :: Pp :: Qp :: alpha :: nil) (Pp :: Qp :: Rp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: alpha :: nil) (P :: Q :: R :: Pp :: Qp :: alpha :: Pp :: Qp :: Rp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: R :: Pp :: Qp :: alpha :: Pp :: Qp :: Rp :: alpha :: nil) ((P :: Q :: R :: Pp :: Qp :: alpha :: nil) ++ (Pp :: Qp :: Rp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpalphamtmp;try rewrite HT2 in HPQRPpQpRpalphamtmp.
	assert(HT := rule_4 (P :: Q :: R :: Pp :: Qp :: alpha :: nil) (Pp :: Qp :: Rp :: alpha :: nil) (Pp :: Qp :: alpha :: nil) 4 3 4 HPQRPpQpRpalphamtmp HPpQpalphamtmp HPQRPpQpalphaMtmp Hincl); apply HT.
}

assert(HPpQpRpalphaM : rk(Pp :: Qp :: Rp :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPpQpRpalpham : rk(Pp :: Qp :: Rp :: alpha ::  nil) >= 1) by (solve_hyps_min HPpQpRpalphaeq HPpQpRpalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LQQpOoalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(Q :: Qp :: Oo :: alpha ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour QQpOoalpha requis par la preuve de (?)QQpOoalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour QQpOoalpha requis par la preuve de (?)QQpOoalpha pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour QQpOoalpha requis par la preuve de (?)QQpOoalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HQQpOoalpham2 : rk(Q :: Qp :: Oo :: alpha :: nil) >= 2).
{
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Q :: Qp :: nil) (Q :: Qp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: Qp :: nil) (Q :: Qp :: Oo :: alpha :: nil) 2 2 HQQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -2 et 5*)
assert(HQQpOoalphaM3 : rk(Q :: Qp :: Oo :: alpha :: nil) <= 3).
{
	assert(HQQpOoMtmp : rk(Q :: Qp :: Oo :: nil) <= 2) by (solve_hyps_max HQQpOoeq HQQpOoM2).
	assert(HalphaMtmp : rk(alpha :: nil) <= 1) by (solve_hyps_max Halphaeq HalphaM1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Q :: Qp :: Oo :: nil) (alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Q :: Qp :: Oo :: alpha :: nil) (Q :: Qp :: Oo :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Qp :: Oo :: alpha :: nil) ((Q :: Qp :: Oo :: nil) ++ (alpha :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Q :: Qp :: Oo :: nil) (alpha :: nil) (nil) 2 1 0 HQQpOoMtmp HalphaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 -2 et -4*)
(* ensembles concernés AUB : P :: Q :: R :: Qp :: Oo :: alpha ::  de rang :  4 et 4 	 AiB : alpha ::  de rang :  1 et 1 	 A : P :: R :: alpha ::   de rang : 2 et 2 *)
assert(HQQpOoalpham3 : rk(Q :: Qp :: Oo :: alpha :: nil) >= 3).
{
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	assert(HPQRQpOoalphaeq : rk(P :: Q :: R :: Qp :: Oo :: alpha :: nil) = 4) by (apply LPQRQpOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQRQpOoalphamtmp : rk(P :: Q :: R :: Qp :: Oo :: alpha :: nil) >= 4) by (solve_hyps_min HPQRQpOoalphaeq HPQRQpOoalpham4).
	assert(Halphamtmp : rk(alpha :: nil) >= 1) by (solve_hyps_min Halphaeq Halpham1).
	assert(Hincl : incl (alpha :: nil) (list_inter (P :: R :: alpha :: nil) (Q :: Qp :: Oo :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Qp :: Oo :: alpha :: nil) (P :: R :: alpha :: Q :: Qp :: Oo :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: alpha :: Q :: Qp :: Oo :: alpha :: nil) ((P :: R :: alpha :: nil) ++ (Q :: Qp :: Oo :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRQpOoalphamtmp;try rewrite HT2 in HPQRQpOoalphamtmp.
	assert(HT := rule_4 (P :: R :: alpha :: nil) (Q :: Qp :: Oo :: alpha :: nil) (alpha :: nil) 4 1 2 HPQRQpOoalphamtmp Halphamtmp HPRalphaMtmp Hincl); apply HT.
}

assert(HQQpOoalphaM : rk(Q :: Qp :: Oo :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HQQpOoalpham : rk(Q :: Qp :: Oo :: alpha ::  nil) >= 1) by (solve_hyps_min HQQpOoalphaeq HQQpOoalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPQRQpRpOoalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Q :: R :: Qp :: Rp :: Oo :: alpha ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRQpRpOoalpha requis par la preuve de (?)PQRQpRpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRQpRp requis par la preuve de (?)PQRQpRpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRQpRp requis par la preuve de (?)PQRQpRp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: -4 -2 et -4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Rp ::  de rang :  4 et 4 	 AiB : P ::  de rang :  1 et 1 	 A : P :: Pp ::   de rang : 2 et 2 *)
assert(HPQRQpRpm3 : rk(P :: Q :: R :: Qp :: Rp :: nil) >= 3).
{
	assert(HPPpMtmp : rk(P :: Pp :: nil) <= 2) by (solve_hyps_max HPPpeq HPPpM2).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(HPmtmp : rk(P :: nil) >= 1) by (solve_hyps_min HPeq HPm1).
	assert(Hincl : incl (P :: nil) (list_inter (P :: Pp :: nil) (P :: Q :: R :: Qp :: Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Pp :: P :: Q :: R :: Qp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: P :: Q :: R :: Qp :: Rp :: nil) ((P :: Pp :: nil) ++ (P :: Q :: R :: Qp :: Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_4 (P :: Pp :: nil) (P :: Q :: R :: Qp :: Rp :: nil) (P :: nil) 4 1 2 HPQRPpQpRpmtmp HPmtmp HPPpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRQpRpOoalpha requis par la preuve de (?)PQRQpRpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRQpRpOoalpha requis par la preuve de (?)PQRQpRpOoalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRQpRpOoalpham2 : rk(P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: nil) >= 2).
{
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Q :: Qp :: nil) (P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: Qp :: nil) (P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: nil) 2 2 HQQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPQRQpRpOoalpham3 : rk(P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: nil) >= 3).
{
	assert(HPQRQpRpmtmp : rk(P :: Q :: R :: Qp :: Rp :: nil) >= 3) by (solve_hyps_min HPQRQpRpeq HPQRQpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Qp :: Rp :: nil) (P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Qp :: Rp :: nil) (P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: nil) 3 3 HPQRQpRpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRQpRpOoalpham4 : rk(P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

assert(HPQRQpRpOoalphaM : rk(P :: Q :: R :: Qp :: Rp :: Oo :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRQpRpOoalpham : rk(P :: Q :: R :: Qp :: Rp :: Oo :: alpha ::  nil) >= 1) by (solve_hyps_min HPQRQpRpOoalphaeq HPQRQpRpOoalpham1).
intuition.
Qed.

(* dans constructLemma(), requis par LQbeta *)
(* dans constructLemma(), requis par LQPpQpbeta *)
(* dans constructLemma(), requis par LQPpQpOoalphabeta *)
(* dans la couche 0 *)
Lemma LQPpQpRpOoalphabeta : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(Q :: Pp :: Qp :: Rp :: Oo :: alpha :: beta ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour QPpQpRpOoalphabeta requis par la preuve de (?)QPpQpRpOoalphabeta pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour QPpQpRpOoalphabeta requis par la preuve de (?)QPpQpRpOoalphabeta pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HQPpQpRpOoalphabetam2 : rk(Q :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: nil) >= 2).
{
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Q :: Qp :: nil) (Q :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: Qp :: nil) (Q :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: nil) 2 2 HQQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HQPpQpRpOoalphabetam4 : rk(Q :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: nil) >= 4).
{
	assert(HPpQpRpOomtmp : rk(Pp :: Qp :: Rp :: Oo :: nil) >= 4) by (solve_hyps_min HPpQpRpOoeq HPpQpRpOom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: Rp :: Oo :: nil) (Q :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: Rp :: Oo :: nil) (Q :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: nil) 4 4 HPpQpRpOomtmp Hcomp Hincl);apply HT.
}

assert(HQPpQpRpOoalphabetaM : rk(Q :: Pp :: Qp :: Rp :: Oo :: alpha :: beta ::  nil) <= 4) by (apply rk_upper_dim).
assert(HQPpQpRpOoalphabetam : rk(Q :: Pp :: Qp :: Rp :: Oo :: alpha :: beta ::  nil) >= 1) by (solve_hyps_min HQPpQpRpOoalphabetaeq HQPpQpRpOoalphabetam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LQPpQpOoalphabeta : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(Q :: Pp :: Qp :: Oo :: alpha :: beta ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour QPpQpOoalphabeta requis par la preuve de (?)QPpQpOoalphabeta pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour PQRPpQpOoalphabeta requis par la preuve de (?)QPpQpOoalphabeta pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQpOoalphabeta requis par la preuve de (?)PQRPpQpOoalphabeta pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQpOoalphabeta pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpm2 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -1 et -2*)
assert(HPQRPpQpm3 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3).
{
	assert(HRpMtmp : rk(Rp :: nil) <= 1) by (solve_hyps_max HRpeq HRpM1).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) ((P :: Q :: R :: Pp :: Qp :: nil) ++ (Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_2 (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil) (nil) 4 0 1 HPQRPpQpRpmtmp Hmtmp HRpMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQpOoalphabeta requis par la preuve de (?)PQRPpQpOoalphabeta pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQpOoalphabeta requis par la preuve de (?)PQRPpQpOoalphabeta pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpOoalphabetam2 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPQRPpQpOoalphabetam3 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: nil) >= 3).
{
	assert(HPQRPpQpmtmp : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3) by (solve_hyps_min HPQRPpQpeq HPQRPpQpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: nil) 3 3 HPQRPpQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpOoalphabetam4 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour QPpQpOoalphabeta requis par la preuve de (?)QPpQpOoalphabeta pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour QPpQpOoalphabeta requis par la preuve de (?)QPpQpOoalphabeta pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HQPpQpOoalphabetam2 : rk(Q :: Pp :: Qp :: Oo :: alpha :: beta :: nil) >= 2).
{
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Q :: Qp :: nil) (Q :: Pp :: Qp :: Oo :: alpha :: beta :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: Qp :: nil) (Q :: Pp :: Qp :: Oo :: alpha :: beta :: nil) 2 2 HQQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta ::  de rang :  4 et 4 	 AiB : alpha ::  de rang :  1 et 1 	 A : P :: R :: alpha ::   de rang : 2 et 2 *)
assert(HQPpQpOoalphabetam3 : rk(Q :: Pp :: Qp :: Oo :: alpha :: beta :: nil) >= 3).
{
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	assert(HPQRPpQpOoalphabetamtmp : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: nil) >= 4) by (solve_hyps_min HPQRPpQpOoalphabetaeq HPQRPpQpOoalphabetam4).
	assert(Halphamtmp : rk(alpha :: nil) >= 1) by (solve_hyps_min Halphaeq Halpham1).
	assert(Hincl : incl (alpha :: nil) (list_inter (P :: R :: alpha :: nil) (Q :: Pp :: Qp :: Oo :: alpha :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: nil) (P :: R :: alpha :: Q :: Pp :: Qp :: Oo :: alpha :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: alpha :: Q :: Pp :: Qp :: Oo :: alpha :: beta :: nil) ((P :: R :: alpha :: nil) ++ (Q :: Pp :: Qp :: Oo :: alpha :: beta :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpOoalphabetamtmp;try rewrite HT2 in HPQRPpQpOoalphabetamtmp.
	assert(HT := rule_4 (P :: R :: alpha :: nil) (Q :: Pp :: Qp :: Oo :: alpha :: beta :: nil) (alpha :: nil) 4 1 2 HPQRPpQpOoalphabetamtmp Halphamtmp HPRalphaMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et -4*)
(* ensembles concernés AUB : Q :: Pp :: Qp :: Rp :: Oo :: alpha :: beta ::  de rang :  4 et 4 	 AiB : Pp :: alpha ::  de rang :  2 et 2 	 A : Pp :: Rp :: alpha ::   de rang : 2 et 2 *)
assert(HQPpQpOoalphabetam4 : rk(Q :: Pp :: Qp :: Oo :: alpha :: beta :: nil) >= 4).
{
	assert(HPpRpalphaMtmp : rk(Pp :: Rp :: alpha :: nil) <= 2) by (solve_hyps_max HPpRpalphaeq HPpRpalphaM2).
	assert(HQPpQpRpOoalphabetaeq : rk(Q :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: nil) = 4) by (apply LQPpQpRpOoalphabeta with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HQPpQpRpOoalphabetamtmp : rk(Q :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: nil) >= 4) by (solve_hyps_min HQPpQpRpOoalphabetaeq HQPpQpRpOoalphabetam4).
	assert(HPpalphaeq : rk(Pp :: alpha :: nil) = 2) by (apply LPpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpalphamtmp : rk(Pp :: alpha :: nil) >= 2) by (solve_hyps_min HPpalphaeq HPpalpham2).
	assert(Hincl : incl (Pp :: alpha :: nil) (list_inter (Pp :: Rp :: alpha :: nil) (Q :: Pp :: Qp :: Oo :: alpha :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Q :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: nil) (Pp :: Rp :: alpha :: Q :: Pp :: Qp :: Oo :: alpha :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: Rp :: alpha :: Q :: Pp :: Qp :: Oo :: alpha :: beta :: nil) ((Pp :: Rp :: alpha :: nil) ++ (Q :: Pp :: Qp :: Oo :: alpha :: beta :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HQPpQpRpOoalphabetamtmp;try rewrite HT2 in HQPpQpRpOoalphabetamtmp.
	assert(HT := rule_4 (Pp :: Rp :: alpha :: nil) (Q :: Pp :: Qp :: Oo :: alpha :: beta :: nil) (Pp :: alpha :: nil) 4 2 2 HQPpQpRpOoalphabetamtmp HPpalphamtmp HPpRpalphaMtmp Hincl); apply HT.
}

assert(HQPpQpOoalphabetaM : rk(Q :: Pp :: Qp :: Oo :: alpha :: beta ::  nil) <= 4) by (apply rk_upper_dim).
assert(HQPpQpOoalphabetam : rk(Q :: Pp :: Qp :: Oo :: alpha :: beta ::  nil) >= 1) by (solve_hyps_min HQPpQpOoalphabetaeq HQPpQpOoalphabetam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LQPpQpbeta : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(Q :: Pp :: Qp :: beta ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour QPpQpbeta requis par la preuve de (?)QPpQpbeta pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour QPpQpbeta requis par la preuve de (?)QPpQpbeta pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour QPpQpbeta requis par la preuve de (?)QPpQpbeta pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HQPpQpbetaM3 : rk(Q :: Pp :: Qp :: beta :: nil) <= 3).
{
	assert(HQMtmp : rk(Q :: nil) <= 1) by (solve_hyps_max HQeq HQM1).
	assert(HPpQpbetaMtmp : rk(Pp :: Qp :: beta :: nil) <= 2) by (solve_hyps_max HPpQpbetaeq HPpQpbetaM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Q :: nil) (Pp :: Qp :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Q :: Pp :: Qp :: beta :: nil) (Q :: Pp :: Qp :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Pp :: Qp :: beta :: nil) ((Q :: nil) ++ (Pp :: Qp :: beta :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Q :: nil) (Pp :: Qp :: beta :: nil) (nil) 1 2 0 HQMtmp HPpQpbetaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HQPpQpbetam2 : rk(Q :: Pp :: Qp :: beta :: nil) >= 2).
{
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Q :: Qp :: nil) (Q :: Pp :: Qp :: beta :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: Qp :: nil) (Q :: Pp :: Qp :: beta :: nil) 2 2 HQQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 -4 et 4*)
(* ensembles concernés AUB : Q :: Pp :: Qp :: Oo :: alpha :: beta ::  de rang :  4 et 4 	 AiB : Q :: Qp ::  de rang :  2 et 2 	 A : Q :: Qp :: Oo :: alpha ::   de rang : 3 et 3 *)
assert(HQPpQpbetam3 : rk(Q :: Pp :: Qp :: beta :: nil) >= 3).
{
	assert(HQQpOoalphaeq : rk(Q :: Qp :: Oo :: alpha :: nil) = 3) by (apply LQQpOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HQQpOoalphaMtmp : rk(Q :: Qp :: Oo :: alpha :: nil) <= 3) by (solve_hyps_max HQQpOoalphaeq HQQpOoalphaM3).
	assert(HQPpQpOoalphabetaeq : rk(Q :: Pp :: Qp :: Oo :: alpha :: beta :: nil) = 4) by (apply LQPpQpOoalphabeta with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HQPpQpOoalphabetamtmp : rk(Q :: Pp :: Qp :: Oo :: alpha :: beta :: nil) >= 4) by (solve_hyps_min HQPpQpOoalphabetaeq HQPpQpOoalphabetam4).
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hincl : incl (Q :: Qp :: nil) (list_inter (Q :: Qp :: Oo :: alpha :: nil) (Q :: Pp :: Qp :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Q :: Pp :: Qp :: Oo :: alpha :: beta :: nil) (Q :: Qp :: Oo :: alpha :: Q :: Pp :: Qp :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Qp :: Oo :: alpha :: Q :: Pp :: Qp :: beta :: nil) ((Q :: Qp :: Oo :: alpha :: nil) ++ (Q :: Pp :: Qp :: beta :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HQPpQpOoalphabetamtmp;try rewrite HT2 in HQPpQpOoalphabetamtmp.
	assert(HT := rule_4 (Q :: Qp :: Oo :: alpha :: nil) (Q :: Pp :: Qp :: beta :: nil) (Q :: Qp :: nil) 4 2 3 HQPpQpOoalphabetamtmp HQQpmtmp HQQpOoalphaMtmp Hincl); apply HT.
}

assert(HQPpQpbetaM : rk(Q :: Pp :: Qp :: beta ::  nil) <= 4) by (apply rk_upper_dim).
assert(HQPpQpbetam : rk(Q :: Pp :: Qp :: beta ::  nil) >= 1) by (solve_hyps_min HQPpQpbetaeq HQPpQpbetam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LQbeta : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(Q :: beta ::  nil) = 2.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour Qbeta requis par la preuve de (?)Qbeta pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -2 et -4*)
assert(HQbetam2 : rk(Q :: beta :: nil) >= 2).
{
	assert(HPpQpbetaMtmp : rk(Pp :: Qp :: beta :: nil) <= 2) by (solve_hyps_max HPpQpbetaeq HPpQpbetaM2).
	assert(HQPpQpbetaeq : rk(Q :: Pp :: Qp :: beta :: nil) = 3) by (apply LQPpQpbeta with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HQPpQpbetamtmp : rk(Q :: Pp :: Qp :: beta :: nil) >= 3) by (solve_hyps_min HQPpQpbetaeq HQPpQpbetam3).
	assert(Hbetamtmp : rk(beta :: nil) >= 1) by (solve_hyps_min Hbetaeq Hbetam1).
	assert(Hincl : incl (beta :: nil) (list_inter (Q :: beta :: nil) (Pp :: Qp :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Q :: Pp :: Qp :: beta :: nil) (Q :: beta :: Pp :: Qp :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: beta :: Pp :: Qp :: beta :: nil) ((Q :: beta :: nil) ++ (Pp :: Qp :: beta :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HQPpQpbetamtmp;try rewrite HT2 in HQPpQpbetamtmp.
	assert(HT := rule_2 (Q :: beta :: nil) (Pp :: Qp :: beta :: nil) (beta :: nil) 3 1 2 HQPpQpbetamtmp Hbetamtmp HPpQpbetaMtmp Hincl);apply HT.
}

assert(HQbetaM : rk(Q :: beta ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HQbetaeq HQbetaM2).
assert(HQbetam : rk(Q :: beta ::  nil) >= 1) by (solve_hyps_min HQbetaeq HQbetam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPQRPpQpOoalphabeta : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQpOoalphabeta requis par la preuve de (?)PQRPpQpOoalphabeta pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQpOoalphabeta pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpm2 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -1 et -2*)
assert(HPQRPpQpm3 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3).
{
	assert(HRpMtmp : rk(Rp :: nil) <= 1) by (solve_hyps_max HRpeq HRpM1).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) ((P :: Q :: R :: Pp :: Qp :: nil) ++ (Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_2 (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil) (nil) 4 0 1 HPQRPpQpRpmtmp Hmtmp HRpMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQpOoalphabeta requis par la preuve de (?)PQRPpQpOoalphabeta pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQpOoalphabeta requis par la preuve de (?)PQRPpQpOoalphabeta pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpOoalphabetam2 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPQRPpQpOoalphabetam3 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: nil) >= 3).
{
	assert(HPQRPpQpmtmp : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3) by (solve_hyps_min HPQRPpQpeq HPQRPpQpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: nil) 3 3 HPQRPpQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpOoalphabetam4 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

assert(HPQRPpQpOoalphabetaM : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRPpQpOoalphabetam : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta ::  nil) >= 1) by (solve_hyps_min HPQRPpQpOoalphabetaeq HPQRPpQpOoalphabetam1).
intuition.
Qed.

(* dans constructLemma(), requis par LQgamma *)
(* dans constructLemma(), requis par LQQpRpgamma *)
(* dans constructLemma(), requis par LQQpRpOoalphagamma *)
(* dans la couche 0 *)
Lemma LQPpQpRpOoalphagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour QPpQpRpOoalphagamma requis par la preuve de (?)QPpQpRpOoalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour QPpQpRpOoalphagamma requis par la preuve de (?)QPpQpRpOoalphagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HQPpQpRpOoalphagammam2 : rk(Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 2).
{
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Q :: Qp :: nil) (Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: Qp :: nil) (Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) 2 2 HQQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HQPpQpRpOoalphagammam4 : rk(Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 4).
{
	assert(HPpQpRpOomtmp : rk(Pp :: Qp :: Rp :: Oo :: nil) >= 4) by (solve_hyps_min HPpQpRpOoeq HPpQpRpOom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: Rp :: Oo :: nil) (Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: Rp :: Oo :: nil) (Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) 4 4 HPpQpRpOomtmp Hcomp Hincl);apply HT.
}

assert(HQPpQpRpOoalphagammaM : rk(Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HQPpQpRpOoalphagammam : rk(Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma ::  nil) >= 1) by (solve_hyps_min HQPpQpRpOoalphagammaeq HQPpQpRpOoalphagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LQQpRpOoalphagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(Q :: Qp :: Rp :: Oo :: alpha :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour QQpRpOoalphagamma requis par la preuve de (?)QQpRpOoalphagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour PQRQpRpOoalphagamma requis par la preuve de (?)QQpRpOoalphagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRQpRpOoalphagamma requis par la preuve de (?)PQRQpRpOoalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRQpRp requis par la preuve de (?)PQRQpRpOoalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRQpRp requis par la preuve de (?)PQRQpRp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: -4 -2 et -4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Rp ::  de rang :  4 et 4 	 AiB : P ::  de rang :  1 et 1 	 A : P :: Pp ::   de rang : 2 et 2 *)
assert(HPQRQpRpm3 : rk(P :: Q :: R :: Qp :: Rp :: nil) >= 3).
{
	assert(HPPpMtmp : rk(P :: Pp :: nil) <= 2) by (solve_hyps_max HPPpeq HPPpM2).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(HPmtmp : rk(P :: nil) >= 1) by (solve_hyps_min HPeq HPm1).
	assert(Hincl : incl (P :: nil) (list_inter (P :: Pp :: nil) (P :: Q :: R :: Qp :: Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Pp :: P :: Q :: R :: Qp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: P :: Q :: R :: Qp :: Rp :: nil) ((P :: Pp :: nil) ++ (P :: Q :: R :: Qp :: Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_4 (P :: Pp :: nil) (P :: Q :: R :: Qp :: Rp :: nil) (P :: nil) 4 1 2 HPQRPpQpRpmtmp HPmtmp HPPpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRQpRpOoalphagamma requis par la preuve de (?)PQRQpRpOoalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRQpRpOoalphagamma requis par la preuve de (?)PQRQpRpOoalphagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRQpRpOoalphagammam2 : rk(P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 2).
{
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Q :: Qp :: nil) (P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: Qp :: nil) (P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) 2 2 HQQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPQRQpRpOoalphagammam3 : rk(P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 3).
{
	assert(HPQRQpRpmtmp : rk(P :: Q :: R :: Qp :: Rp :: nil) >= 3) by (solve_hyps_min HPQRQpRpeq HPQRQpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Qp :: Rp :: nil) (P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Qp :: Rp :: nil) (P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) 3 3 HPQRQpRpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRQpRpOoalphagammam4 : rk(P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour QQpRpOoalphagamma requis par la preuve de (?)QQpRpOoalphagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour QQpRpOoalphagamma requis par la preuve de (?)QQpRpOoalphagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HQQpRpOoalphagammam2 : rk(Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 2).
{
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Q :: Qp :: nil) (Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: Qp :: nil) (Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) 2 2 HQQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: gamma ::  de rang :  4 et 4 	 AiB : alpha ::  de rang :  1 et 1 	 A : P :: R :: alpha ::   de rang : 2 et 2 *)
assert(HQQpRpOoalphagammam3 : rk(Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 3).
{
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	assert(HPQRQpRpOoalphagammamtmp : rk(P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 4) by (solve_hyps_min HPQRQpRpOoalphagammaeq HPQRQpRpOoalphagammam4).
	assert(Halphamtmp : rk(alpha :: nil) >= 1) by (solve_hyps_min Halphaeq Halpham1).
	assert(Hincl : incl (alpha :: nil) (list_inter (P :: R :: alpha :: nil) (Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) (P :: R :: alpha :: Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: alpha :: Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) ((P :: R :: alpha :: nil) ++ (Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRQpRpOoalphagammamtmp;try rewrite HT2 in HPQRQpRpOoalphagammamtmp.
	assert(HT := rule_4 (P :: R :: alpha :: nil) (Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) (alpha :: nil) 4 1 2 HPQRQpRpOoalphagammamtmp Halphamtmp HPRalphaMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et -4*)
(* ensembles concernés AUB : Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma ::  de rang :  4 et 4 	 AiB : Rp :: alpha ::  de rang :  2 et 2 	 A : Pp :: Rp :: alpha ::   de rang : 2 et 2 *)
assert(HQQpRpOoalphagammam4 : rk(Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 4).
{
	assert(HPpRpalphaMtmp : rk(Pp :: Rp :: alpha :: nil) <= 2) by (solve_hyps_max HPpRpalphaeq HPpRpalphaM2).
	assert(HQPpQpRpOoalphagammaeq : rk(Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) = 4) by (apply LQPpQpRpOoalphagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HQPpQpRpOoalphagammamtmp : rk(Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 4) by (solve_hyps_min HQPpQpRpOoalphagammaeq HQPpQpRpOoalphagammam4).
	assert(HRpalphaeq : rk(Rp :: alpha :: nil) = 2) by (apply LRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HRpalphamtmp : rk(Rp :: alpha :: nil) >= 2) by (solve_hyps_min HRpalphaeq HRpalpham2).
	assert(Hincl : incl (Rp :: alpha :: nil) (list_inter (Pp :: Rp :: alpha :: nil) (Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) (Pp :: Rp :: alpha :: Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: Rp :: alpha :: Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) ((Pp :: Rp :: alpha :: nil) ++ (Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HQPpQpRpOoalphagammamtmp;try rewrite HT2 in HQPpQpRpOoalphagammamtmp.
	assert(HT := rule_4 (Pp :: Rp :: alpha :: nil) (Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) (Rp :: alpha :: nil) 4 2 2 HQPpQpRpOoalphagammamtmp HRpalphamtmp HPpRpalphaMtmp Hincl); apply HT.
}

assert(HQQpRpOoalphagammaM : rk(Q :: Qp :: Rp :: Oo :: alpha :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HQQpRpOoalphagammam : rk(Q :: Qp :: Rp :: Oo :: alpha :: gamma ::  nil) >= 1) by (solve_hyps_min HQQpRpOoalphagammaeq HQQpRpOoalphagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LQQpRpgamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(Q :: Qp :: Rp :: gamma ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour QQpRpgamma requis par la preuve de (?)QQpRpgamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour QQpRpgamma requis par la preuve de (?)QQpRpgamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour QQpRpgamma requis par la preuve de (?)QQpRpgamma pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HQQpRpgammaM3 : rk(Q :: Qp :: Rp :: gamma :: nil) <= 3).
{
	assert(HQMtmp : rk(Q :: nil) <= 1) by (solve_hyps_max HQeq HQM1).
	assert(HQpRpgammaMtmp : rk(Qp :: Rp :: gamma :: nil) <= 2) by (solve_hyps_max HQpRpgammaeq HQpRpgammaM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Q :: nil) (Qp :: Rp :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Q :: Qp :: Rp :: gamma :: nil) (Q :: Qp :: Rp :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Qp :: Rp :: gamma :: nil) ((Q :: nil) ++ (Qp :: Rp :: gamma :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Q :: nil) (Qp :: Rp :: gamma :: nil) (nil) 1 2 0 HQMtmp HQpRpgammaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HQQpRpgammam2 : rk(Q :: Qp :: Rp :: gamma :: nil) >= 2).
{
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Q :: Qp :: nil) (Q :: Qp :: Rp :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: Qp :: nil) (Q :: Qp :: Rp :: gamma :: nil) 2 2 HQQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 -4 et 4*)
(* ensembles concernés AUB : Q :: Qp :: Rp :: Oo :: alpha :: gamma ::  de rang :  4 et 4 	 AiB : Q :: Qp ::  de rang :  2 et 2 	 A : Q :: Qp :: Oo :: alpha ::   de rang : 3 et 3 *)
assert(HQQpRpgammam3 : rk(Q :: Qp :: Rp :: gamma :: nil) >= 3).
{
	assert(HQQpOoalphaeq : rk(Q :: Qp :: Oo :: alpha :: nil) = 3) by (apply LQQpOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HQQpOoalphaMtmp : rk(Q :: Qp :: Oo :: alpha :: nil) <= 3) by (solve_hyps_max HQQpOoalphaeq HQQpOoalphaM3).
	assert(HQQpRpOoalphagammaeq : rk(Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) = 4) by (apply LQQpRpOoalphagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HQQpRpOoalphagammamtmp : rk(Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 4) by (solve_hyps_min HQQpRpOoalphagammaeq HQQpRpOoalphagammam4).
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hincl : incl (Q :: Qp :: nil) (list_inter (Q :: Qp :: Oo :: alpha :: nil) (Q :: Qp :: Rp :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) (Q :: Qp :: Oo :: alpha :: Q :: Qp :: Rp :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Qp :: Oo :: alpha :: Q :: Qp :: Rp :: gamma :: nil) ((Q :: Qp :: Oo :: alpha :: nil) ++ (Q :: Qp :: Rp :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HQQpRpOoalphagammamtmp;try rewrite HT2 in HQQpRpOoalphagammamtmp.
	assert(HT := rule_4 (Q :: Qp :: Oo :: alpha :: nil) (Q :: Qp :: Rp :: gamma :: nil) (Q :: Qp :: nil) 4 2 3 HQQpRpOoalphagammamtmp HQQpmtmp HQQpOoalphaMtmp Hincl); apply HT.
}

assert(HQQpRpgammaM : rk(Q :: Qp :: Rp :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HQQpRpgammam : rk(Q :: Qp :: Rp :: gamma ::  nil) >= 1) by (solve_hyps_min HQQpRpgammaeq HQQpRpgammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LQgamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(Q :: gamma ::  nil) = 2.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour Qgamma requis par la preuve de (?)Qgamma pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -2 et -4*)
assert(HQgammam2 : rk(Q :: gamma :: nil) >= 2).
{
	assert(HQpRpgammaMtmp : rk(Qp :: Rp :: gamma :: nil) <= 2) by (solve_hyps_max HQpRpgammaeq HQpRpgammaM2).
	assert(HQQpRpgammaeq : rk(Q :: Qp :: Rp :: gamma :: nil) = 3) by (apply LQQpRpgamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HQQpRpgammamtmp : rk(Q :: Qp :: Rp :: gamma :: nil) >= 3) by (solve_hyps_min HQQpRpgammaeq HQQpRpgammam3).
	assert(Hgammamtmp : rk(gamma :: nil) >= 1) by (solve_hyps_min Hgammaeq Hgammam1).
	assert(Hincl : incl (gamma :: nil) (list_inter (Q :: gamma :: nil) (Qp :: Rp :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Q :: Qp :: Rp :: gamma :: nil) (Q :: gamma :: Qp :: Rp :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: gamma :: Qp :: Rp :: gamma :: nil) ((Q :: gamma :: nil) ++ (Qp :: Rp :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HQQpRpgammamtmp;try rewrite HT2 in HQQpRpgammamtmp.
	assert(HT := rule_2 (Q :: gamma :: nil) (Qp :: Rp :: gamma :: nil) (gamma :: nil) 3 1 2 HQQpRpgammamtmp Hgammamtmp HQpRpgammaMtmp Hincl);apply HT.
}

assert(HQgammaM : rk(Q :: gamma ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HQgammaeq HQgammaM2).
assert(HQgammam : rk(Q :: gamma ::  nil) >= 1) by (solve_hyps_min HQgammaeq HQgammam1).
intuition.
Qed.

(* dans constructLemma(), requis par LPQgamma *)
(* dans constructLemma(), requis par LPQRgamma *)
(* dans la couche 0 *)
Lemma LPQRPpOogamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Oo :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpOogamma requis par la preuve de (?)PQRPpOogamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpOogamma requis par la preuve de (?)PQRPpOogamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpOogammam2 : rk(P :: Q :: R :: Pp :: Oo :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Oo :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Oo :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpOogammam4 : rk(P :: Q :: R :: Pp :: Oo :: gamma :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Oo :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Oo :: gamma :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

assert(HPQRPpOogammaM : rk(P :: Q :: R :: Pp :: Oo :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRPpOogammam : rk(P :: Q :: R :: Pp :: Oo :: gamma ::  nil) >= 1) by (solve_hyps_min HPQRPpOogammaeq HPQRPpOogammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPQRgamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Q :: R :: gamma ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PQRgamma requis par la preuve de (?)PQRgamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour PpOo requis par la preuve de (?)PQRgamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour PQRgamma requis par la preuve de (?)PQRgamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRgamma requis par la preuve de (?)PQRgamma pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HPQRgammaM3 : rk(P :: Q :: R :: gamma :: nil) <= 3).
{
	assert(HPMtmp : rk(P :: nil) <= 1) by (solve_hyps_max HPeq HPM1).
	assert(HQRgammaMtmp : rk(Q :: R :: gamma :: nil) <= 2) by (solve_hyps_max HQRgammaeq HQRgammaM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P :: nil) (Q :: R :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: gamma :: nil) (P :: Q :: R :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: R :: gamma :: nil) ((P :: nil) ++ (Q :: R :: gamma :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P :: nil) (Q :: R :: gamma :: nil) (nil) 1 2 0 HPMtmp HQRgammaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 4 -1 et 5*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Oo :: gamma ::  de rang :  4 et 4 	 AiB :  de rang :  0 et 0 	 A : Pp :: Oo ::   de rang : 1 et 2 *)
assert(HPQRgammam2 : rk(P :: Q :: R :: gamma :: nil) >= 2).
{
	assert(HPpOoMtmp : rk(Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPpOoeq HPpOoM2).
	assert(HPQRPpOogammaeq : rk(P :: Q :: R :: Pp :: Oo :: gamma :: nil) = 4) by (apply LPQRPpOogamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQRPpOogammamtmp : rk(P :: Q :: R :: Pp :: Oo :: gamma :: nil) >= 4) by (solve_hyps_min HPQRPpOogammaeq HPQRPpOogammam4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Pp :: Oo :: nil) (P :: Q :: R :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Oo :: gamma :: nil) (Pp :: Oo :: P :: Q :: R :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: Oo :: P :: Q :: R :: gamma :: nil) ((Pp :: Oo :: nil) ++ (P :: Q :: R :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpOogammamtmp;try rewrite HT2 in HPQRPpOogammamtmp.
	assert(HT := rule_4 (Pp :: Oo :: nil) (P :: Q :: R :: gamma :: nil) (nil) 4 0 2 HPQRPpOogammamtmp Hmtmp HPpOoMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 -2 et -4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Oo :: gamma ::  de rang :  4 et 4 	 AiB : P ::  de rang :  1 et 1 	 A : P :: Pp :: Oo ::   de rang : 2 et 2 *)
assert(HPQRgammam3 : rk(P :: Q :: R :: gamma :: nil) >= 3).
{
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	assert(HPQRPpOogammaeq : rk(P :: Q :: R :: Pp :: Oo :: gamma :: nil) = 4) by (apply LPQRPpOogamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQRPpOogammamtmp : rk(P :: Q :: R :: Pp :: Oo :: gamma :: nil) >= 4) by (solve_hyps_min HPQRPpOogammaeq HPQRPpOogammam4).
	assert(HPmtmp : rk(P :: nil) >= 1) by (solve_hyps_min HPeq HPm1).
	assert(Hincl : incl (P :: nil) (list_inter (P :: Pp :: Oo :: nil) (P :: Q :: R :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Oo :: gamma :: nil) (P :: Pp :: Oo :: P :: Q :: R :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Oo :: P :: Q :: R :: gamma :: nil) ((P :: Pp :: Oo :: nil) ++ (P :: Q :: R :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpOogammamtmp;try rewrite HT2 in HPQRPpOogammamtmp.
	assert(HT := rule_4 (P :: Pp :: Oo :: nil) (P :: Q :: R :: gamma :: nil) (P :: nil) 4 1 2 HPQRPpOogammamtmp HPmtmp HPPpOoMtmp Hincl); apply HT.
}

assert(HPQRgammaM : rk(P :: Q :: R :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRgammam : rk(P :: Q :: R :: gamma ::  nil) >= 1) by (solve_hyps_min HPQRgammaeq HPQRgammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPQgamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Q :: gamma ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PQgamma requis par la preuve de (?)PQgamma pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour PQgamma requis par la preuve de (?)PQgamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 4 -2 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Oo :: gamma ::  de rang :  4 et 4 	 AiB : P ::  de rang :  1 et 1 	 A : P :: R :: Pp :: Oo ::   de rang : 3 et 3 *)
assert(HPQgammam2 : rk(P :: Q :: gamma :: nil) >= 2).
{
	assert(HPRPpOoeq : rk(P :: R :: Pp :: Oo :: nil) = 3) by (apply LPRPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPRPpOoMtmp : rk(P :: R :: Pp :: Oo :: nil) <= 3) by (solve_hyps_max HPRPpOoeq HPRPpOoM3).
	assert(HPQRPpOogammaeq : rk(P :: Q :: R :: Pp :: Oo :: gamma :: nil) = 4) by (apply LPQRPpOogamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQRPpOogammamtmp : rk(P :: Q :: R :: Pp :: Oo :: gamma :: nil) >= 4) by (solve_hyps_min HPQRPpOogammaeq HPQRPpOogammam4).
	assert(HPmtmp : rk(P :: nil) >= 1) by (solve_hyps_min HPeq HPm1).
	assert(Hincl : incl (P :: nil) (list_inter (P :: R :: Pp :: Oo :: nil) (P :: Q :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Oo :: gamma :: nil) (P :: R :: Pp :: Oo :: P :: Q :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: Pp :: Oo :: P :: Q :: gamma :: nil) ((P :: R :: Pp :: Oo :: nil) ++ (P :: Q :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpOogammamtmp;try rewrite HT2 in HPQRPpOogammamtmp.
	assert(HT := rule_4 (P :: R :: Pp :: Oo :: nil) (P :: Q :: gamma :: nil) (P :: nil) 4 1 3 HPQRPpOogammamtmp HPmtmp HPRPpOoMtmp Hincl); apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et -4*)
assert(HPQgammam3 : rk(P :: Q :: gamma :: nil) >= 3).
{
	assert(HQRgammaMtmp : rk(Q :: R :: gamma :: nil) <= 2) by (solve_hyps_max HQRgammaeq HQRgammaM2).
	assert(HPQRgammaeq : rk(P :: Q :: R :: gamma :: nil) = 3) by (apply LPQRgamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQRgammamtmp : rk(P :: Q :: R :: gamma :: nil) >= 3) by (solve_hyps_min HPQRgammaeq HPQRgammam3).
	assert(HQgammaeq : rk(Q :: gamma :: nil) = 2) by (apply LQgamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HQgammamtmp : rk(Q :: gamma :: nil) >= 2) by (solve_hyps_min HQgammaeq HQgammam2).
	assert(Hincl : incl (Q :: gamma :: nil) (list_inter (P :: Q :: gamma :: nil) (Q :: R :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: gamma :: nil) (P :: Q :: gamma :: Q :: R :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: gamma :: Q :: R :: gamma :: nil) ((P :: Q :: gamma :: nil) ++ (Q :: R :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRgammamtmp;try rewrite HT2 in HPQRgammamtmp.
	assert(HT := rule_2 (P :: Q :: gamma :: nil) (Q :: R :: gamma :: nil) (Q :: gamma :: nil) 3 2 2 HPQRgammamtmp HQgammamtmp HQRgammaMtmp Hincl);apply HT.
}

assert(HPQgammaM : rk(P :: Q :: gamma ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HPQgammaeq HPQgammaM3).
assert(HPQgammam : rk(P :: Q :: gamma ::  nil) >= 1) by (solve_hyps_min HPQgammaeq HPQgammam1).
intuition.
Qed.

(* dans constructLemma(), requis par LQpgamma *)
(* dans constructLemma(), requis par LQRQpgamma *)
(* dans la couche 0 *)
Lemma LQRQpOogamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(Q :: R :: Qp :: Oo :: gamma ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour QRQpOogamma requis par la preuve de (?)QRQpOogamma pour la règle 1  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour PQRPpQpOogamma requis par la preuve de (?)QRQpOogamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQpOogamma requis par la preuve de (?)PQRPpQpOogamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQpOogamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpm2 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -1 et -2*)
assert(HPQRPpQpm3 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3).
{
	assert(HRpMtmp : rk(Rp :: nil) <= 1) by (solve_hyps_max HRpeq HRpM1).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) ((P :: Q :: R :: Pp :: Qp :: nil) ++ (Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_2 (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil) (nil) 4 0 1 HPQRPpQpRpmtmp Hmtmp HRpMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQpOogamma requis par la preuve de (?)PQRPpQpOogamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQpOogamma requis par la preuve de (?)PQRPpQpOogamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpOogammam2 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPQRPpQpOogammam3 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) >= 3).
{
	assert(HPQRPpQpmtmp : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3) by (solve_hyps_min HPQRPpQpeq HPQRPpQpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) 3 3 HPQRPpQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpOogammam4 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour QRQpOogamma requis par la preuve de (?)QRQpOogamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour QRQpOogamma requis par la preuve de (?)QRQpOogamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HQRQpOogammam2 : rk(Q :: R :: Qp :: Oo :: gamma :: nil) >= 2).
{
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Q :: Qp :: nil) (Q :: R :: Qp :: Oo :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: Qp :: nil) (Q :: R :: Qp :: Oo :: gamma :: nil) 2 2 HQQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Oo :: gamma ::  de rang :  4 et 4 	 AiB : Oo ::  de rang :  1 et 1 	 A : P :: Pp :: Oo ::   de rang : 2 et 2 *)
assert(HQRQpOogammam3 : rk(Q :: R :: Qp :: Oo :: gamma :: nil) >= 3).
{
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	assert(HPQRPpQpOogammamtmp : rk(P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) >= 4) by (solve_hyps_min HPQRPpQpOogammaeq HPQRPpQpOogammam4).
	assert(HOomtmp : rk(Oo :: nil) >= 1) by (solve_hyps_min HOoeq HOom1).
	assert(Hincl : incl (Oo :: nil) (list_inter (P :: Pp :: Oo :: nil) (Q :: R :: Qp :: Oo :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) (P :: Pp :: Oo :: Q :: R :: Qp :: Oo :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Oo :: Q :: R :: Qp :: Oo :: gamma :: nil) ((P :: Pp :: Oo :: nil) ++ (Q :: R :: Qp :: Oo :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpOogammamtmp;try rewrite HT2 in HPQRPpQpOogammamtmp.
	assert(HT := rule_4 (P :: Pp :: Oo :: nil) (Q :: R :: Qp :: Oo :: gamma :: nil) (Oo :: nil) 4 1 2 HPQRPpQpOogammamtmp HOomtmp HPPpOoMtmp Hincl); apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -2*)
assert(HQRQpOogammaM3 : rk(Q :: R :: Qp :: Oo :: gamma :: nil) <= 3).
{
	assert(HQQpOoMtmp : rk(Q :: Qp :: Oo :: nil) <= 2) by (solve_hyps_max HQQpOoeq HQQpOoM2).
	assert(HQRgammaMtmp : rk(Q :: R :: gamma :: nil) <= 2) by (solve_hyps_max HQRgammaeq HQRgammaM2).
	assert(HQmtmp : rk(Q :: nil) >= 1) by (solve_hyps_min HQeq HQm1).
	assert(Hincl : incl (Q :: nil) (list_inter (Q :: Qp :: Oo :: nil) (Q :: R :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Q :: R :: Qp :: Oo :: gamma :: nil) (Q :: Qp :: Oo :: Q :: R :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Qp :: Oo :: Q :: R :: gamma :: nil) ((Q :: Qp :: Oo :: nil) ++ (Q :: R :: gamma :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Q :: Qp :: Oo :: nil) (Q :: R :: gamma :: nil) (Q :: nil) 2 2 1 HQQpOoMtmp HQRgammaMtmp HQmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HQRQpOogammaM : rk(Q :: R :: Qp :: Oo :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HQRQpOogammam : rk(Q :: R :: Qp :: Oo :: gamma ::  nil) >= 1) by (solve_hyps_min HQRQpOogammaeq HQRQpOogammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LQRQpgamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(Q :: R :: Qp :: gamma ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour QRQpgamma requis par la preuve de (?)QRQpgamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour QRQpgamma requis par la preuve de (?)QRQpgamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour QRQpgamma requis par la preuve de (?)QRQpgamma pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HQRQpgammaM3 : rk(Q :: R :: Qp :: gamma :: nil) <= 3).
{
	assert(HQpMtmp : rk(Qp :: nil) <= 1) by (solve_hyps_max HQpeq HQpM1).
	assert(HQRgammaMtmp : rk(Q :: R :: gamma :: nil) <= 2) by (solve_hyps_max HQRgammaeq HQRgammaM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Qp :: nil) (Q :: R :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Q :: R :: Qp :: gamma :: nil) (Qp :: Q :: R :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Qp :: Q :: R :: gamma :: nil) ((Qp :: nil) ++ (Q :: R :: gamma :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Qp :: nil) (Q :: R :: gamma :: nil) (nil) 1 2 0 HQpMtmp HQRgammaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HQRQpgammam2 : rk(Q :: R :: Qp :: gamma :: nil) >= 2).
{
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Q :: Qp :: nil) (Q :: R :: Qp :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: Qp :: nil) (Q :: R :: Qp :: gamma :: nil) 2 2 HQQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 -4 et -4*)
(* ensembles concernés AUB : Q :: R :: Qp :: Oo :: gamma ::  de rang :  3 et 3 	 AiB : Q :: Qp ::  de rang :  2 et 2 	 A : Q :: Qp :: Oo ::   de rang : 2 et 2 *)
assert(HQRQpgammam3 : rk(Q :: R :: Qp :: gamma :: nil) >= 3).
{
	assert(HQQpOoMtmp : rk(Q :: Qp :: Oo :: nil) <= 2) by (solve_hyps_max HQQpOoeq HQQpOoM2).
	assert(HQRQpOogammaeq : rk(Q :: R :: Qp :: Oo :: gamma :: nil) = 3) by (apply LQRQpOogamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HQRQpOogammamtmp : rk(Q :: R :: Qp :: Oo :: gamma :: nil) >= 3) by (solve_hyps_min HQRQpOogammaeq HQRQpOogammam3).
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hincl : incl (Q :: Qp :: nil) (list_inter (Q :: Qp :: Oo :: nil) (Q :: R :: Qp :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Q :: R :: Qp :: Oo :: gamma :: nil) (Q :: Qp :: Oo :: Q :: R :: Qp :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Qp :: Oo :: Q :: R :: Qp :: gamma :: nil) ((Q :: Qp :: Oo :: nil) ++ (Q :: R :: Qp :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HQRQpOogammamtmp;try rewrite HT2 in HQRQpOogammamtmp.
	assert(HT := rule_4 (Q :: Qp :: Oo :: nil) (Q :: R :: Qp :: gamma :: nil) (Q :: Qp :: nil) 3 2 2 HQRQpOogammamtmp HQQpmtmp HQQpOoMtmp Hincl); apply HT.
}

assert(HQRQpgammaM : rk(Q :: R :: Qp :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HQRQpgammam : rk(Q :: R :: Qp :: gamma ::  nil) >= 1) by (solve_hyps_min HQRQpgammaeq HQRQpgammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LQpgamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(Qp :: gamma ::  nil) = 2.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour Qpgamma requis par la preuve de (?)Qpgamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 2) *)
(* marque des antécédents AUB AiB A: 4 -2 et -4*)
(* ensembles concernés AUB : Q :: R :: Qp :: gamma ::  de rang :  3 et 3 	 AiB : gamma ::  de rang :  1 et 1 	 A : Q :: R :: gamma ::   de rang : 2 et 2 *)
assert(HQpgammam2 : rk(Qp :: gamma :: nil) >= 2).
{
	assert(HQRgammaMtmp : rk(Q :: R :: gamma :: nil) <= 2) by (solve_hyps_max HQRgammaeq HQRgammaM2).
	assert(HQRQpgammaeq : rk(Q :: R :: Qp :: gamma :: nil) = 3) by (apply LQRQpgamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HQRQpgammamtmp : rk(Q :: R :: Qp :: gamma :: nil) >= 3) by (solve_hyps_min HQRQpgammaeq HQRQpgammam3).
	assert(Hgammamtmp : rk(gamma :: nil) >= 1) by (solve_hyps_min Hgammaeq Hgammam1).
	assert(Hincl : incl (gamma :: nil) (list_inter (Q :: R :: gamma :: nil) (Qp :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Q :: R :: Qp :: gamma :: nil) (Q :: R :: gamma :: Qp :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: R :: gamma :: Qp :: gamma :: nil) ((Q :: R :: gamma :: nil) ++ (Qp :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HQRQpgammamtmp;try rewrite HT2 in HQRQpgammamtmp.
	assert(HT := rule_4 (Q :: R :: gamma :: nil) (Qp :: gamma :: nil) (gamma :: nil) 3 1 2 HQRQpgammamtmp Hgammamtmp HQRgammaMtmp Hincl); apply HT.
}

assert(HQpgammaM : rk(Qp :: gamma ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HQpgammaeq HQpgammaM2).
assert(HQpgammam : rk(Qp :: gamma ::  nil) >= 1) by (solve_hyps_min HQpgammaeq HQpgammam1).
intuition.
Qed.

(* dans constructLemma(), requis par LPpQpgamma *)
(* dans la couche 0 *)
Lemma LPpQpRpOogamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(Pp :: Qp :: Rp :: Oo :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PpQpRpOogamma requis par la preuve de (?)PpQpRpOogamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPpQpRpOogammam4 : rk(Pp :: Qp :: Rp :: Oo :: gamma :: nil) >= 4).
{
	assert(HPpQpRpOomtmp : rk(Pp :: Qp :: Rp :: Oo :: nil) >= 4) by (solve_hyps_min HPpQpRpOoeq HPpQpRpOom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: Rp :: Oo :: nil) (Pp :: Qp :: Rp :: Oo :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: Rp :: Oo :: nil) (Pp :: Qp :: Rp :: Oo :: gamma :: nil) 4 4 HPpQpRpOomtmp Hcomp Hincl);apply HT.
}

assert(HPpQpRpOogammaM : rk(Pp :: Qp :: Rp :: Oo :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPpQpRpOogammam : rk(Pp :: Qp :: Rp :: Oo :: gamma ::  nil) >= 1) by (solve_hyps_min HPpQpRpOogammaeq HPpQpRpOogammam1).
intuition.
Qed.

(* dans constructLemma(), requis par LPpQpgamma *)
(* dans constructLemma(), requis par LQpRpOogamma *)
(* dans la couche 0 *)
Lemma LPpQpRpOoalphagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(Pp :: Qp :: Rp :: Oo :: alpha :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PpQpRpOoalphagamma requis par la preuve de (?)PpQpRpOoalphagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPpQpRpOoalphagammam4 : rk(Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 4).
{
	assert(HPpQpRpOomtmp : rk(Pp :: Qp :: Rp :: Oo :: nil) >= 4) by (solve_hyps_min HPpQpRpOoeq HPpQpRpOom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: Rp :: Oo :: nil) (Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: Rp :: Oo :: nil) (Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) 4 4 HPpQpRpOomtmp Hcomp Hincl);apply HT.
}

assert(HPpQpRpOoalphagammaM : rk(Pp :: Qp :: Rp :: Oo :: alpha :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPpQpRpOoalphagammam : rk(Pp :: Qp :: Rp :: Oo :: alpha :: gamma ::  nil) >= 1) by (solve_hyps_min HPpQpRpOoalphagammaeq HPpQpRpOoalphagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LQpRpOogamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(Qp :: Rp :: Oo :: gamma ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour QpRpOogamma requis par la preuve de (?)QpRpOogamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour QpRpOogamma requis par la preuve de (?)QpRpOogamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour QpRpOogamma requis par la preuve de (?)QpRpOogamma pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HQpRpOogammaM3 : rk(Qp :: Rp :: Oo :: gamma :: nil) <= 3).
{
	assert(HOoMtmp : rk(Oo :: nil) <= 1) by (solve_hyps_max HOoeq HOoM1).
	assert(HQpRpgammaMtmp : rk(Qp :: Rp :: gamma :: nil) <= 2) by (solve_hyps_max HQpRpgammaeq HQpRpgammaM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Oo :: nil) (Qp :: Rp :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Qp :: Rp :: Oo :: gamma :: nil) (Oo :: Qp :: Rp :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: Qp :: Rp :: gamma :: nil) ((Oo :: nil) ++ (Qp :: Rp :: gamma :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Oo :: nil) (Qp :: Rp :: gamma :: nil) (nil) 1 2 0 HOoMtmp HQpRpgammaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 4 -1 et 4*)
(* ensembles concernés AUB : Pp :: Qp :: Rp :: Oo :: alpha :: gamma ::  de rang :  4 et 4 	 AiB :  de rang :  0 et 0 	 A : Pp :: alpha ::   de rang : 2 et 2 *)
assert(HQpRpOogammam2 : rk(Qp :: Rp :: Oo :: gamma :: nil) >= 2).
{
	assert(HPpalphaeq : rk(Pp :: alpha :: nil) = 2) by (apply LPpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpalphaMtmp : rk(Pp :: alpha :: nil) <= 2) by (solve_hyps_max HPpalphaeq HPpalphaM2).
	assert(HPpQpRpOoalphagammaeq : rk(Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) = 4) by (apply LPpQpRpOoalphagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpQpRpOoalphagammamtmp : rk(Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 4) by (solve_hyps_min HPpQpRpOoalphagammaeq HPpQpRpOoalphagammam4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Pp :: alpha :: nil) (Qp :: Rp :: Oo :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) (Pp :: alpha :: Qp :: Rp :: Oo :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: alpha :: Qp :: Rp :: Oo :: gamma :: nil) ((Pp :: alpha :: nil) ++ (Qp :: Rp :: Oo :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPpQpRpOoalphagammamtmp;try rewrite HT2 in HPpQpRpOoalphagammamtmp.
	assert(HT := rule_4 (Pp :: alpha :: nil) (Qp :: Rp :: Oo :: gamma :: nil) (nil) 4 0 2 HPpQpRpOoalphagammamtmp Hmtmp HPpalphaMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 -2 et -4*)
(* ensembles concernés AUB : Pp :: Qp :: Rp :: Oo :: alpha :: gamma ::  de rang :  4 et 4 	 AiB : Rp ::  de rang :  1 et 1 	 A : Pp :: Rp :: alpha ::   de rang : 2 et 2 *)
assert(HQpRpOogammam3 : rk(Qp :: Rp :: Oo :: gamma :: nil) >= 3).
{
	assert(HPpRpalphaMtmp : rk(Pp :: Rp :: alpha :: nil) <= 2) by (solve_hyps_max HPpRpalphaeq HPpRpalphaM2).
	assert(HPpQpRpOoalphagammaeq : rk(Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) = 4) by (apply LPpQpRpOoalphagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpQpRpOoalphagammamtmp : rk(Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 4) by (solve_hyps_min HPpQpRpOoalphagammaeq HPpQpRpOoalphagammam4).
	assert(HRpmtmp : rk(Rp :: nil) >= 1) by (solve_hyps_min HRpeq HRpm1).
	assert(Hincl : incl (Rp :: nil) (list_inter (Pp :: Rp :: alpha :: nil) (Qp :: Rp :: Oo :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) (Pp :: Rp :: alpha :: Qp :: Rp :: Oo :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: Rp :: alpha :: Qp :: Rp :: Oo :: gamma :: nil) ((Pp :: Rp :: alpha :: nil) ++ (Qp :: Rp :: Oo :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPpQpRpOoalphagammamtmp;try rewrite HT2 in HPpQpRpOoalphagammamtmp.
	assert(HT := rule_4 (Pp :: Rp :: alpha :: nil) (Qp :: Rp :: Oo :: gamma :: nil) (Rp :: nil) 4 1 2 HPpQpRpOoalphagammamtmp HRpmtmp HPpRpalphaMtmp Hincl); apply HT.
}

assert(HQpRpOogammaM : rk(Qp :: Rp :: Oo :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HQpRpOogammam : rk(Qp :: Rp :: Oo :: gamma ::  nil) >= 1) by (solve_hyps_min HQpRpOogammaeq HQpRpOogammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPpQpgamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(Pp :: Qp :: gamma ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PpQpgamma requis par la preuve de (?)PpQpgamma pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PpQpRpalphagamma requis par la preuve de (?)PpQpgamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PpQpRpalphagamma requis par la preuve de (?)PpQpRpalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRPpQpRpalphagamma requis par la preuve de (?)PpQpRpalphagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRPpQpRp requis par la preuve de (?)PRPpQpRpalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour QPp requis par la preuve de (?)PRPpQpRp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpQpRp requis par la preuve de (?)PRPpQpRp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpQpRp requis par la preuve de (?)PRPpQpRp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPRPpQpRpm2 : rk(P :: R :: Pp :: Qp :: Rp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: -4 -2 et 5*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Rp ::  de rang :  4 et 4 	 AiB : Pp ::  de rang :  1 et 1 	 A : Q :: Pp ::   de rang : 1 et 2 *)
assert(HPRPpQpRpm3 : rk(P :: R :: Pp :: Qp :: Rp :: nil) >= 3).
{
	assert(HQPpMtmp : rk(Q :: Pp :: nil) <= 2) by (solve_hyps_max HQPpeq HQPpM2).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(HPpmtmp : rk(Pp :: nil) >= 1) by (solve_hyps_min HPpeq HPpm1).
	assert(Hincl : incl (Pp :: nil) (list_inter (Q :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (Q :: Pp :: P :: R :: Pp :: Qp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Pp :: P :: R :: Pp :: Qp :: Rp :: nil) ((Q :: Pp :: nil) ++ (P :: R :: Pp :: Qp :: Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_4 (Q :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: nil) (Pp :: nil) 4 1 2 HPQRPpQpRpmtmp HPpmtmp HQPpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpQpRpalphagamma requis par la preuve de (?)PRPpQpRpalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpQpRpalphagamma requis par la preuve de (?)PRPpQpRpalphagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPRPpQpRpalphagammam2 : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPRPpQpRpalphagammam3 : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: gamma :: nil) >= 3).
{
	assert(HPRPpQpRpmtmp : rk(P :: R :: Pp :: Qp :: Rp :: nil) >= 3) by (solve_hyps_min HPRPpQpRpeq HPRPpQpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: R :: Pp :: Qp :: Rp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: R :: Pp :: Qp :: Rp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: gamma :: nil) 3 3 HPRPpQpRpmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PpQpRpalphagamma requis par la preuve de (?)PpQpRpalphagamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : P :: R :: Pp :: Qp :: Rp :: alpha :: gamma ::  de rang :  3 et 4 	 AiB : alpha ::  de rang :  1 et 1 	 A : P :: R :: alpha ::   de rang : 2 et 2 *)
assert(HPpQpRpalphagammam2 : rk(Pp :: Qp :: Rp :: alpha :: gamma :: nil) >= 2).
{
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	assert(HPRPpQpRpalphagammamtmp : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: gamma :: nil) >= 3) by (solve_hyps_min HPRPpQpRpalphagammaeq HPRPpQpRpalphagammam3).
	assert(Halphamtmp : rk(alpha :: nil) >= 1) by (solve_hyps_min Halphaeq Halpham1).
	assert(Hincl : incl (alpha :: nil) (list_inter (P :: R :: alpha :: nil) (Pp :: Qp :: Rp :: alpha :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: Qp :: Rp :: alpha :: gamma :: nil) (P :: R :: alpha :: Pp :: Qp :: Rp :: alpha :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: alpha :: Pp :: Qp :: Rp :: alpha :: gamma :: nil) ((P :: R :: alpha :: nil) ++ (Pp :: Qp :: Rp :: alpha :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPRPpQpRpalphagammamtmp;try rewrite HT2 in HPRPpQpRpalphagammamtmp.
	assert(HT := rule_4 (P :: R :: alpha :: nil) (Pp :: Qp :: Rp :: alpha :: gamma :: nil) (alpha :: nil) 3 1 2 HPRPpQpRpalphagammamtmp Halphamtmp HPRalphaMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPpQpRpalphagammam3 : rk(Pp :: Qp :: Rp :: alpha :: gamma :: nil) >= 3).
{
	assert(HPpQpalphaeq : rk(Pp :: Qp :: alpha :: nil) = 3) by (apply LPpQpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpQpalphamtmp : rk(Pp :: Qp :: alpha :: nil) >= 3) by (solve_hyps_min HPpQpalphaeq HPpQpalpham3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: alpha :: nil) (Pp :: Qp :: Rp :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: alpha :: nil) (Pp :: Qp :: Rp :: alpha :: gamma :: nil) 3 3 HPpQpalphamtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour PpQpgamma requis par la preuve de (?)PpQpgamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : Pp :: Qp :: Rp :: alpha :: gamma ::  de rang :  3 et 4 	 AiB : Pp ::  de rang :  1 et 1 	 A : Pp :: Rp :: alpha ::   de rang : 2 et 2 *)
assert(HPpQpgammam2 : rk(Pp :: Qp :: gamma :: nil) >= 2).
{
	assert(HPpRpalphaMtmp : rk(Pp :: Rp :: alpha :: nil) <= 2) by (solve_hyps_max HPpRpalphaeq HPpRpalphaM2).
	assert(HPpQpRpalphagammamtmp : rk(Pp :: Qp :: Rp :: alpha :: gamma :: nil) >= 3) by (solve_hyps_min HPpQpRpalphagammaeq HPpQpRpalphagammam3).
	assert(HPpmtmp : rk(Pp :: nil) >= 1) by (solve_hyps_min HPpeq HPpm1).
	assert(Hincl : incl (Pp :: nil) (list_inter (Pp :: Rp :: alpha :: nil) (Pp :: Qp :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Pp :: Qp :: Rp :: alpha :: gamma :: nil) (Pp :: Rp :: alpha :: Pp :: Qp :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: Rp :: alpha :: Pp :: Qp :: gamma :: nil) ((Pp :: Rp :: alpha :: nil) ++ (Pp :: Qp :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPpQpRpalphagammamtmp;try rewrite HT2 in HPpQpRpalphagammamtmp.
	assert(HT := rule_4 (Pp :: Rp :: alpha :: nil) (Pp :: Qp :: gamma :: nil) (Pp :: nil) 3 1 2 HPpQpRpalphagammamtmp HPpmtmp HPpRpalphaMtmp Hincl); apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 4*)
assert(HPpQpgammam3 : rk(Pp :: Qp :: gamma :: nil) >= 3).
{
	assert(HQpRpOogammaeq : rk(Qp :: Rp :: Oo :: gamma :: nil) = 3) by (apply LQpRpOogamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HQpRpOogammaMtmp : rk(Qp :: Rp :: Oo :: gamma :: nil) <= 3) by (solve_hyps_max HQpRpOogammaeq HQpRpOogammaM3).
	assert(HPpQpRpOogammaeq : rk(Pp :: Qp :: Rp :: Oo :: gamma :: nil) = 4) by (apply LPpQpRpOogamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpQpRpOogammamtmp : rk(Pp :: Qp :: Rp :: Oo :: gamma :: nil) >= 4) by (solve_hyps_min HPpQpRpOogammaeq HPpQpRpOogammam4).
	assert(HQpgammaeq : rk(Qp :: gamma :: nil) = 2) by (apply LQpgamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HQpgammamtmp : rk(Qp :: gamma :: nil) >= 2) by (solve_hyps_min HQpgammaeq HQpgammam2).
	assert(Hincl : incl (Qp :: gamma :: nil) (list_inter (Pp :: Qp :: gamma :: nil) (Qp :: Rp :: Oo :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Pp :: Qp :: Rp :: Oo :: gamma :: nil) (Pp :: Qp :: gamma :: Qp :: Rp :: Oo :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: Qp :: gamma :: Qp :: Rp :: Oo :: gamma :: nil) ((Pp :: Qp :: gamma :: nil) ++ (Qp :: Rp :: Oo :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPpQpRpOogammamtmp;try rewrite HT2 in HPpQpRpOogammamtmp.
	assert(HT := rule_2 (Pp :: Qp :: gamma :: nil) (Qp :: Rp :: Oo :: gamma :: nil) (Qp :: gamma :: nil) 4 2 3 HPpQpRpOogammamtmp HQpgammamtmp HQpRpOogammaMtmp Hincl);apply HT.
}

assert(HPpQpgammaM : rk(Pp :: Qp :: gamma ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HPpQpgammaeq HPpQpgammaM3).
assert(HPpQpgammam : rk(Pp :: Qp :: gamma ::  nil) >= 1) by (solve_hyps_min HPpQpgammaeq HPpQpgammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPQRPpQpOogamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Oo :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQpOogamma requis par la preuve de (?)PQRPpQpOogamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQpOogamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpm2 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -1 et -2*)
assert(HPQRPpQpm3 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3).
{
	assert(HRpMtmp : rk(Rp :: nil) <= 1) by (solve_hyps_max HRpeq HRpM1).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) ((P :: Q :: R :: Pp :: Qp :: nil) ++ (Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_2 (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil) (nil) 4 0 1 HPQRPpQpRpmtmp Hmtmp HRpMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQpOogamma requis par la preuve de (?)PQRPpQpOogamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQpOogamma requis par la preuve de (?)PQRPpQpOogamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpOogammam2 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPQRPpQpOogammam3 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) >= 3).
{
	assert(HPQRPpQpmtmp : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3) by (solve_hyps_min HPQRPpQpeq HPQRPpQpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) 3 3 HPQRPpQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpOogammam4 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

assert(HPQRPpQpOogammaM : rk(P :: Q :: R :: Pp :: Qp :: Oo :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRPpQpOogammam : rk(P :: Q :: R :: Pp :: Qp :: Oo :: gamma ::  nil) >= 1) by (solve_hyps_min HPQRPpQpOogammaeq HPQRPpQpOogammam1).
intuition.
Qed.

(* dans constructLemma(), requis par LPQalphagamma *)
(* dans la couche 0 *)
Lemma LPQRalphagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Q :: R :: alpha :: gamma ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRalphagamma requis par la preuve de (?)PQRalphagamma pour la règle 1  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour PQRPpOoalphagamma requis par la preuve de (?)PQRalphagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpOoalphagamma requis par la preuve de (?)PQRPpOoalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpOoalphagamma requis par la preuve de (?)PQRPpOoalphagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpOoalphagammam2 : rk(P :: Q :: R :: Pp :: Oo :: alpha :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Oo :: alpha :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpOoalphagammam4 : rk(P :: Q :: R :: Pp :: Oo :: alpha :: gamma :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Oo :: alpha :: gamma :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRalphagamma requis par la preuve de (?)PQRalphagamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Oo :: alpha :: gamma ::  de rang :  4 et 4 	 AiB : P ::  de rang :  1 et 1 	 A : P :: Pp :: Oo ::   de rang : 2 et 2 *)
assert(HPQRalphagammam3 : rk(P :: Q :: R :: alpha :: gamma :: nil) >= 3).
{
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	assert(HPQRPpOoalphagammamtmp : rk(P :: Q :: R :: Pp :: Oo :: alpha :: gamma :: nil) >= 4) by (solve_hyps_min HPQRPpOoalphagammaeq HPQRPpOoalphagammam4).
	assert(HPmtmp : rk(P :: nil) >= 1) by (solve_hyps_min HPeq HPm1).
	assert(Hincl : incl (P :: nil) (list_inter (P :: Pp :: Oo :: nil) (P :: Q :: R :: alpha :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Oo :: alpha :: gamma :: nil) (P :: Pp :: Oo :: P :: Q :: R :: alpha :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Oo :: P :: Q :: R :: alpha :: gamma :: nil) ((P :: Pp :: Oo :: nil) ++ (P :: Q :: R :: alpha :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpOoalphagammamtmp;try rewrite HT2 in HPQRPpOoalphagammamtmp.
	assert(HT := rule_4 (P :: Pp :: Oo :: nil) (P :: Q :: R :: alpha :: gamma :: nil) (P :: nil) 4 1 2 HPQRPpOoalphagammamtmp HPmtmp HPPpOoMtmp Hincl); apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -2*)
assert(HPQRalphagammaM3 : rk(P :: Q :: R :: alpha :: gamma :: nil) <= 3).
{
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	assert(HQRgammaMtmp : rk(Q :: R :: gamma :: nil) <= 2) by (solve_hyps_max HQRgammaeq HQRgammaM2).
	assert(HRmtmp : rk(R :: nil) >= 1) by (solve_hyps_min HReq HRm1).
	assert(Hincl : incl (R :: nil) (list_inter (P :: R :: alpha :: nil) (Q :: R :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: alpha :: gamma :: nil) (P :: R :: alpha :: Q :: R :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: alpha :: Q :: R :: gamma :: nil) ((P :: R :: alpha :: nil) ++ (Q :: R :: gamma :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P :: R :: alpha :: nil) (Q :: R :: gamma :: nil) (R :: nil) 2 2 1 HPRalphaMtmp HQRgammaMtmp HRmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HPQRalphagammaM : rk(P :: Q :: R :: alpha :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRalphagammam : rk(P :: Q :: R :: alpha :: gamma ::  nil) >= 1) by (solve_hyps_min HPQRalphagammaeq HPQRalphagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPQalphagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Q :: alpha :: gamma ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQalphagamma requis par la preuve de (?)PQalphagamma pour la règle 6  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQalphagamma requis par la preuve de (?)PQalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour PQRPpOoalphagamma requis par la preuve de (?)PQalphagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpOoalphagamma requis par la preuve de (?)PQRPpOoalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpOoalphagamma requis par la preuve de (?)PQRPpOoalphagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpOoalphagammam2 : rk(P :: Q :: R :: Pp :: Oo :: alpha :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Oo :: alpha :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpOoalphagammam4 : rk(P :: Q :: R :: Pp :: Oo :: alpha :: gamma :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Oo :: alpha :: gamma :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQalphagamma requis par la preuve de (?)PQalphagamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Oo :: alpha :: gamma ::  de rang :  4 et 4 	 AiB : P ::  de rang :  1 et 1 	 A : P :: R :: Pp :: Oo ::   de rang : 3 et 3 *)
assert(HPQalphagammam2 : rk(P :: Q :: alpha :: gamma :: nil) >= 2).
{
	assert(HPRPpOoeq : rk(P :: R :: Pp :: Oo :: nil) = 3) by (apply LPRPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPRPpOoMtmp : rk(P :: R :: Pp :: Oo :: nil) <= 3) by (solve_hyps_max HPRPpOoeq HPRPpOoM3).
	assert(HPQRPpOoalphagammamtmp : rk(P :: Q :: R :: Pp :: Oo :: alpha :: gamma :: nil) >= 4) by (solve_hyps_min HPQRPpOoalphagammaeq HPQRPpOoalphagammam4).
	assert(HPmtmp : rk(P :: nil) >= 1) by (solve_hyps_min HPeq HPm1).
	assert(Hincl : incl (P :: nil) (list_inter (P :: R :: Pp :: Oo :: nil) (P :: Q :: alpha :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Oo :: alpha :: gamma :: nil) (P :: R :: Pp :: Oo :: P :: Q :: alpha :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: Pp :: Oo :: P :: Q :: alpha :: gamma :: nil) ((P :: R :: Pp :: Oo :: nil) ++ (P :: Q :: alpha :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpOoalphagammamtmp;try rewrite HT2 in HPQRPpOoalphagammamtmp.
	assert(HT := rule_4 (P :: R :: Pp :: Oo :: nil) (P :: Q :: alpha :: gamma :: nil) (P :: nil) 4 1 3 HPQRPpOoalphagammamtmp HPmtmp HPRPpOoMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQalphagammam3 : rk(P :: Q :: alpha :: gamma :: nil) >= 3).
{
	assert(HPQgammaeq : rk(P :: Q :: gamma :: nil) = 3) by (apply LPQgamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQgammamtmp : rk(P :: Q :: gamma :: nil) >= 3) by (solve_hyps_min HPQgammaeq HPQgammam3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: gamma :: nil) (P :: Q :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: gamma :: nil) (P :: Q :: alpha :: gamma :: nil) 3 3 HPQgammamtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 6 (code, 3 ou 4 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQalphagammaM3 : rk(P :: Q :: alpha :: gamma :: nil) <= 3).
{
	assert(HPQRalphagammaeq : rk(P :: Q :: R :: alpha :: gamma :: nil) = 3) by (apply LPQRalphagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQRalphagammaMtmp : rk(P :: Q :: R :: alpha :: gamma :: nil) <= 3) by (solve_hyps_max HPQRalphagammaeq HPQRalphagammaM3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: alpha :: gamma :: nil) (P :: Q :: R :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P :: Q :: alpha :: gamma :: nil) (P :: Q :: R :: alpha :: gamma :: nil) 3 3 HPQRalphagammaMtmp Hcomp Hincl);apply HT.
}

assert(HPQalphagammaM : rk(P :: Q :: alpha :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQalphagammam : rk(P :: Q :: alpha :: gamma ::  nil) >= 1) by (solve_hyps_min HPQalphagammaeq HPQalphagammam1).
intuition.
Qed.

(* dans constructLemma(), requis par LPpQpalphagamma *)
(* dans la couche 0 *)
Lemma LPpQpRpalphagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(Pp :: Qp :: Rp :: alpha :: gamma ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PpQpRpalphagamma requis par la preuve de (?)PpQpRpalphagamma pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PpQpRpalphagamma requis par la preuve de (?)PpQpRpalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRPpQpRpalphagamma requis par la preuve de (?)PpQpRpalphagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRPpQpRp requis par la preuve de (?)PRPpQpRpalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour QPp requis par la preuve de (?)PRPpQpRp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpQpRp requis par la preuve de (?)PRPpQpRp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpQpRp requis par la preuve de (?)PRPpQpRp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPRPpQpRpm2 : rk(P :: R :: Pp :: Qp :: Rp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: -4 -2 et 5*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Rp ::  de rang :  4 et 4 	 AiB : Pp ::  de rang :  1 et 1 	 A : Q :: Pp ::   de rang : 1 et 2 *)
assert(HPRPpQpRpm3 : rk(P :: R :: Pp :: Qp :: Rp :: nil) >= 3).
{
	assert(HQPpMtmp : rk(Q :: Pp :: nil) <= 2) by (solve_hyps_max HQPpeq HQPpM2).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(HPpmtmp : rk(Pp :: nil) >= 1) by (solve_hyps_min HPpeq HPpm1).
	assert(Hincl : incl (Pp :: nil) (list_inter (Q :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (Q :: Pp :: P :: R :: Pp :: Qp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Pp :: P :: R :: Pp :: Qp :: Rp :: nil) ((Q :: Pp :: nil) ++ (P :: R :: Pp :: Qp :: Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_4 (Q :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: nil) (Pp :: nil) 4 1 2 HPQRPpQpRpmtmp HPpmtmp HQPpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpQpRpalphagamma requis par la preuve de (?)PRPpQpRpalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpQpRpalphagamma requis par la preuve de (?)PRPpQpRpalphagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPRPpQpRpalphagammam2 : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPRPpQpRpalphagammam3 : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: gamma :: nil) >= 3).
{
	assert(HPRPpQpRpmtmp : rk(P :: R :: Pp :: Qp :: Rp :: nil) >= 3) by (solve_hyps_min HPRPpQpRpeq HPRPpQpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: R :: Pp :: Qp :: Rp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: R :: Pp :: Qp :: Rp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: gamma :: nil) 3 3 HPRPpQpRpmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PpQpRpalphagamma requis par la preuve de (?)PpQpRpalphagamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : P :: R :: Pp :: Qp :: Rp :: alpha :: gamma ::  de rang :  3 et 4 	 AiB : alpha ::  de rang :  1 et 1 	 A : P :: R :: alpha ::   de rang : 2 et 2 *)
assert(HPpQpRpalphagammam2 : rk(Pp :: Qp :: Rp :: alpha :: gamma :: nil) >= 2).
{
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	assert(HPRPpQpRpalphagammamtmp : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: gamma :: nil) >= 3) by (solve_hyps_min HPRPpQpRpalphagammaeq HPRPpQpRpalphagammam3).
	assert(Halphamtmp : rk(alpha :: nil) >= 1) by (solve_hyps_min Halphaeq Halpham1).
	assert(Hincl : incl (alpha :: nil) (list_inter (P :: R :: alpha :: nil) (Pp :: Qp :: Rp :: alpha :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: Qp :: Rp :: alpha :: gamma :: nil) (P :: R :: alpha :: Pp :: Qp :: Rp :: alpha :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: alpha :: Pp :: Qp :: Rp :: alpha :: gamma :: nil) ((P :: R :: alpha :: nil) ++ (Pp :: Qp :: Rp :: alpha :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPRPpQpRpalphagammamtmp;try rewrite HT2 in HPRPpQpRpalphagammamtmp.
	assert(HT := rule_4 (P :: R :: alpha :: nil) (Pp :: Qp :: Rp :: alpha :: gamma :: nil) (alpha :: nil) 3 1 2 HPRPpQpRpalphagammamtmp Halphamtmp HPRalphaMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPpQpRpalphagammam3 : rk(Pp :: Qp :: Rp :: alpha :: gamma :: nil) >= 3).
{
	assert(HPpQpalphaeq : rk(Pp :: Qp :: alpha :: nil) = 3) by (apply LPpQpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpQpalphamtmp : rk(Pp :: Qp :: alpha :: nil) >= 3) by (solve_hyps_min HPpQpalphaeq HPpQpalpham3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: alpha :: nil) (Pp :: Qp :: Rp :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: alpha :: nil) (Pp :: Qp :: Rp :: alpha :: gamma :: nil) 3 3 HPpQpalphamtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -2*)
assert(HPpQpRpalphagammaM3 : rk(Pp :: Qp :: Rp :: alpha :: gamma :: nil) <= 3).
{
	assert(HPpRpalphaMtmp : rk(Pp :: Rp :: alpha :: nil) <= 2) by (solve_hyps_max HPpRpalphaeq HPpRpalphaM2).
	assert(HQpRpgammaMtmp : rk(Qp :: Rp :: gamma :: nil) <= 2) by (solve_hyps_max HQpRpgammaeq HQpRpgammaM2).
	assert(HRpmtmp : rk(Rp :: nil) >= 1) by (solve_hyps_min HRpeq HRpm1).
	assert(Hincl : incl (Rp :: nil) (list_inter (Pp :: Rp :: alpha :: nil) (Qp :: Rp :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Pp :: Qp :: Rp :: alpha :: gamma :: nil) (Pp :: Rp :: alpha :: Qp :: Rp :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: Rp :: alpha :: Qp :: Rp :: gamma :: nil) ((Pp :: Rp :: alpha :: nil) ++ (Qp :: Rp :: gamma :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Pp :: Rp :: alpha :: nil) (Qp :: Rp :: gamma :: nil) (Rp :: nil) 2 2 1 HPpRpalphaMtmp HQpRpgammaMtmp HRpmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HPpQpRpalphagammaM : rk(Pp :: Qp :: Rp :: alpha :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPpQpRpalphagammam : rk(Pp :: Qp :: Rp :: alpha :: gamma ::  nil) >= 1) by (solve_hyps_min HPpQpRpalphagammaeq HPpQpRpalphagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPpQpalphagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(Pp :: Qp :: alpha :: gamma ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PpQpalphagamma requis par la preuve de (?)PpQpalphagamma pour la règle 6  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PpQpalphagamma requis par la preuve de (?)PpQpalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRPpQpalphagamma requis par la preuve de (?)PpQpalphagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour PQRPpQpOoalphagamma requis par la preuve de (?)PRPpQpalphagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQpOoalphagamma requis par la preuve de (?)PQRPpQpOoalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQpOoalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpm2 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -1 et -2*)
assert(HPQRPpQpm3 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3).
{
	assert(HRpMtmp : rk(Rp :: nil) <= 1) by (solve_hyps_max HRpeq HRpM1).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) ((P :: Q :: R :: Pp :: Qp :: nil) ++ (Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_2 (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil) (nil) 4 0 1 HPQRPpQpRpmtmp Hmtmp HRpMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQpOoalphagamma requis par la preuve de (?)PQRPpQpOoalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQpOoalphagamma requis par la preuve de (?)PQRPpQpOoalphagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpOoalphagammam2 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPQRPpQpOoalphagammam3 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: gamma :: nil) >= 3).
{
	assert(HPQRPpQpmtmp : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3) by (solve_hyps_min HPQRPpQpeq HPQRPpQpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: gamma :: nil) 3 3 HPQRPpQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpOoalphagammam4 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: gamma :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: gamma :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpQpalphagamma requis par la preuve de (?)PRPpQpalphagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpQpalphagamma requis par la preuve de (?)PRPpQpalphagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPRPpQpalphagammam2 : rk(P :: R :: Pp :: Qp :: alpha :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Qp :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Qp :: alpha :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: gamma ::  de rang :  4 et 4 	 AiB : P :: Pp ::  de rang :  2 et 2 	 A : P :: Q :: Pp :: Oo ::   de rang : 3 et 3 *)
assert(HPRPpQpalphagammam3 : rk(P :: R :: Pp :: Qp :: alpha :: gamma :: nil) >= 3).
{
	assert(HPQPpOoeq : rk(P :: Q :: Pp :: Oo :: nil) = 3) by (apply LPQPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQPpOoMtmp : rk(P :: Q :: Pp :: Oo :: nil) <= 3) by (solve_hyps_max HPQPpOoeq HPQPpOoM3).
	assert(HPQRPpQpOoalphagammamtmp : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: gamma :: nil) >= 4) by (solve_hyps_min HPQRPpQpOoalphagammaeq HPQRPpQpOoalphagammam4).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hincl : incl (P :: Pp :: nil) (list_inter (P :: Q :: Pp :: Oo :: nil) (P :: R :: Pp :: Qp :: alpha :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: gamma :: nil) (P :: Q :: Pp :: Oo :: P :: R :: Pp :: Qp :: alpha :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: Pp :: Oo :: P :: R :: Pp :: Qp :: alpha :: gamma :: nil) ((P :: Q :: Pp :: Oo :: nil) ++ (P :: R :: Pp :: Qp :: alpha :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpOoalphagammamtmp;try rewrite HT2 in HPQRPpQpOoalphagammamtmp.
	assert(HT := rule_4 (P :: Q :: Pp :: Oo :: nil) (P :: R :: Pp :: Qp :: alpha :: gamma :: nil) (P :: Pp :: nil) 4 2 3 HPQRPpQpOoalphagammamtmp HPPpmtmp HPQPpOoMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PpQpalphagamma requis par la preuve de (?)PpQpalphagamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : P :: R :: Pp :: Qp :: alpha :: gamma ::  de rang :  3 et 4 	 AiB : alpha ::  de rang :  1 et 1 	 A : P :: R :: alpha ::   de rang : 2 et 2 *)
assert(HPpQpalphagammam2 : rk(Pp :: Qp :: alpha :: gamma :: nil) >= 2).
{
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	assert(HPRPpQpalphagammamtmp : rk(P :: R :: Pp :: Qp :: alpha :: gamma :: nil) >= 3) by (solve_hyps_min HPRPpQpalphagammaeq HPRPpQpalphagammam3).
	assert(Halphamtmp : rk(alpha :: nil) >= 1) by (solve_hyps_min Halphaeq Halpham1).
	assert(Hincl : incl (alpha :: nil) (list_inter (P :: R :: alpha :: nil) (Pp :: Qp :: alpha :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: Qp :: alpha :: gamma :: nil) (P :: R :: alpha :: Pp :: Qp :: alpha :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: alpha :: Pp :: Qp :: alpha :: gamma :: nil) ((P :: R :: alpha :: nil) ++ (Pp :: Qp :: alpha :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPRPpQpalphagammamtmp;try rewrite HT2 in HPRPpQpalphagammamtmp.
	assert(HT := rule_4 (P :: R :: alpha :: nil) (Pp :: Qp :: alpha :: gamma :: nil) (alpha :: nil) 3 1 2 HPRPpQpalphagammamtmp Halphamtmp HPRalphaMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPpQpalphagammam3 : rk(Pp :: Qp :: alpha :: gamma :: nil) >= 3).
{
	assert(HPpQpalphaeq : rk(Pp :: Qp :: alpha :: nil) = 3) by (apply LPpQpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpQpalphamtmp : rk(Pp :: Qp :: alpha :: nil) >= 3) by (solve_hyps_min HPpQpalphaeq HPpQpalpham3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: alpha :: nil) (Pp :: Qp :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: alpha :: nil) (Pp :: Qp :: alpha :: gamma :: nil) 3 3 HPpQpalphamtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 6 (code, 3 ou 4 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPpQpalphagammaM3 : rk(Pp :: Qp :: alpha :: gamma :: nil) <= 3).
{
	assert(HPpQpRpalphagammaeq : rk(Pp :: Qp :: Rp :: alpha :: gamma :: nil) = 3) by (apply LPpQpRpalphagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpQpRpalphagammaMtmp : rk(Pp :: Qp :: Rp :: alpha :: gamma :: nil) <= 3) by (solve_hyps_max HPpQpRpalphagammaeq HPpQpRpalphagammaM3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: alpha :: gamma :: nil) (Pp :: Qp :: Rp :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (Pp :: Qp :: alpha :: gamma :: nil) (Pp :: Qp :: Rp :: alpha :: gamma :: nil) 3 3 HPpQpRpalphagammaMtmp Hcomp Hincl);apply HT.
}

assert(HPpQpalphagammaM : rk(Pp :: Qp :: alpha :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPpQpalphagammam : rk(Pp :: Qp :: alpha :: gamma ::  nil) >= 1) by (solve_hyps_min HPpQpalphagammaeq HPpQpalphagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPQRPpOoalphagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Oo :: alpha :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpOoalphagamma requis par la preuve de (?)PQRPpOoalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpOoalphagamma requis par la preuve de (?)PQRPpOoalphagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpOoalphagammam2 : rk(P :: Q :: R :: Pp :: Oo :: alpha :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Oo :: alpha :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpOoalphagammam4 : rk(P :: Q :: R :: Pp :: Oo :: alpha :: gamma :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Oo :: alpha :: gamma :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

assert(HPQRPpOoalphagammaM : rk(P :: Q :: R :: Pp :: Oo :: alpha :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRPpOoalphagammam : rk(P :: Q :: R :: Pp :: Oo :: alpha :: gamma ::  nil) >= 1) by (solve_hyps_min HPQRPpOoalphagammaeq HPQRPpOoalphagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPQRPpQpOoalphagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQpOoalphagamma requis par la preuve de (?)PQRPpQpOoalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQpOoalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpm2 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -1 et -2*)
assert(HPQRPpQpm3 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3).
{
	assert(HRpMtmp : rk(Rp :: nil) <= 1) by (solve_hyps_max HRpeq HRpM1).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) ((P :: Q :: R :: Pp :: Qp :: nil) ++ (Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_2 (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil) (nil) 4 0 1 HPQRPpQpRpmtmp Hmtmp HRpMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQpOoalphagamma requis par la preuve de (?)PQRPpQpOoalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQpOoalphagamma requis par la preuve de (?)PQRPpQpOoalphagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpOoalphagammam2 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPQRPpQpOoalphagammam3 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: gamma :: nil) >= 3).
{
	assert(HPQRPpQpmtmp : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3) by (solve_hyps_min HPQRPpQpeq HPQRPpQpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: gamma :: nil) 3 3 HPQRPpQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpOoalphagammam4 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: gamma :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: gamma :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

assert(HPQRPpQpOoalphagammaM : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRPpQpOoalphagammam : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: gamma ::  nil) >= 1) by (solve_hyps_min HPQRPpQpOoalphagammaeq HPQRPpQpOoalphagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPQRQpRpOoalphagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRQpRpOoalphagamma requis par la preuve de (?)PQRQpRpOoalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRQpRp requis par la preuve de (?)PQRQpRpOoalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRQpRp requis par la preuve de (?)PQRQpRp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: -4 -2 et -4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Rp ::  de rang :  4 et 4 	 AiB : P ::  de rang :  1 et 1 	 A : P :: Pp ::   de rang : 2 et 2 *)
assert(HPQRQpRpm3 : rk(P :: Q :: R :: Qp :: Rp :: nil) >= 3).
{
	assert(HPPpMtmp : rk(P :: Pp :: nil) <= 2) by (solve_hyps_max HPPpeq HPPpM2).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(HPmtmp : rk(P :: nil) >= 1) by (solve_hyps_min HPeq HPm1).
	assert(Hincl : incl (P :: nil) (list_inter (P :: Pp :: nil) (P :: Q :: R :: Qp :: Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Pp :: P :: Q :: R :: Qp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: P :: Q :: R :: Qp :: Rp :: nil) ((P :: Pp :: nil) ++ (P :: Q :: R :: Qp :: Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_4 (P :: Pp :: nil) (P :: Q :: R :: Qp :: Rp :: nil) (P :: nil) 4 1 2 HPQRPpQpRpmtmp HPmtmp HPPpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRQpRpOoalphagamma requis par la preuve de (?)PQRQpRpOoalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRQpRpOoalphagamma requis par la preuve de (?)PQRQpRpOoalphagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRQpRpOoalphagammam2 : rk(P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 2).
{
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Q :: Qp :: nil) (P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: Qp :: nil) (P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) 2 2 HQQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPQRQpRpOoalphagammam3 : rk(P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 3).
{
	assert(HPQRQpRpmtmp : rk(P :: Q :: R :: Qp :: Rp :: nil) >= 3) by (solve_hyps_min HPQRQpRpeq HPQRQpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Qp :: Rp :: nil) (P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Qp :: Rp :: nil) (P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) 3 3 HPQRQpRpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRQpRpOoalphagammam4 : rk(P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

assert(HPQRQpRpOoalphagammaM : rk(P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRQpRpOoalphagammam : rk(P :: Q :: R :: Qp :: Rp :: Oo :: alpha :: gamma ::  nil) >= 1) by (solve_hyps_min HPQRQpRpOoalphagammaeq HPQRQpRpOoalphagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPQbetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Q :: beta :: gamma ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PQbetagamma requis par la preuve de (?)PQbetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQbetagamma requis par la preuve de (?)PQbetagamma pour la règle 1  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour PQRPpOobetagamma requis par la preuve de (?)PQbetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpOobetagamma requis par la preuve de (?)PQRPpOobetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpOobetagamma requis par la preuve de (?)PQRPpOobetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpOobetagammam2 : rk(P :: Q :: R :: Pp :: Oo :: beta :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Oo :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Oo :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpOobetagammam4 : rk(P :: Q :: R :: Pp :: Oo :: beta :: gamma :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Oo :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Oo :: beta :: gamma :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQbetagamma requis par la preuve de (?)PQbetagamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Oo :: beta :: gamma ::  de rang :  4 et 4 	 AiB : P ::  de rang :  1 et 1 	 A : P :: R :: Pp :: Oo ::   de rang : 3 et 3 *)
assert(HPQbetagammam2 : rk(P :: Q :: beta :: gamma :: nil) >= 2).
{
	assert(HPRPpOoeq : rk(P :: R :: Pp :: Oo :: nil) = 3) by (apply LPRPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPRPpOoMtmp : rk(P :: R :: Pp :: Oo :: nil) <= 3) by (solve_hyps_max HPRPpOoeq HPRPpOoM3).
	assert(HPQRPpOobetagammamtmp : rk(P :: Q :: R :: Pp :: Oo :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPQRPpOobetagammaeq HPQRPpOobetagammam4).
	assert(HPmtmp : rk(P :: nil) >= 1) by (solve_hyps_min HPeq HPm1).
	assert(Hincl : incl (P :: nil) (list_inter (P :: R :: Pp :: Oo :: nil) (P :: Q :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Oo :: beta :: gamma :: nil) (P :: R :: Pp :: Oo :: P :: Q :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: Pp :: Oo :: P :: Q :: beta :: gamma :: nil) ((P :: R :: Pp :: Oo :: nil) ++ (P :: Q :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpOobetagammamtmp;try rewrite HT2 in HPQRPpOobetagammamtmp.
	assert(HT := rule_4 (P :: R :: Pp :: Oo :: nil) (P :: Q :: beta :: gamma :: nil) (P :: nil) 4 1 3 HPQRPpOobetagammamtmp HPmtmp HPRPpOoMtmp Hincl); apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -2 et 5*)
assert(HPQbetagammaM3 : rk(P :: Q :: beta :: gamma :: nil) <= 3).
{
	assert(HPQbetaMtmp : rk(P :: Q :: beta :: nil) <= 2) by (solve_hyps_max HPQbetaeq HPQbetaM2).
	assert(HgammaMtmp : rk(gamma :: nil) <= 1) by (solve_hyps_max Hgammaeq HgammaM1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P :: Q :: beta :: nil) (gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: beta :: gamma :: nil) (P :: Q :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: beta :: gamma :: nil) ((P :: Q :: beta :: nil) ++ (gamma :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P :: Q :: beta :: nil) (gamma :: nil) (nil) 2 1 0 HPQbetaMtmp HgammaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQbetagammam3 : rk(P :: Q :: beta :: gamma :: nil) >= 3).
{
	assert(HPQgammaeq : rk(P :: Q :: gamma :: nil) = 3) by (apply LPQgamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQgammamtmp : rk(P :: Q :: gamma :: nil) >= 3) by (solve_hyps_min HPQgammaeq HPQgammam3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: gamma :: nil) (P :: Q :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: gamma :: nil) (P :: Q :: beta :: gamma :: nil) 3 3 HPQgammamtmp Hcomp Hincl);apply HT.
}

assert(HPQbetagammaM : rk(P :: Q :: beta :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQbetagammam : rk(P :: Q :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min HPQbetagammaeq HPQbetagammam1).
intuition.
Qed.

(* dans constructLemma(), requis par LPpQpbetagamma *)
(* dans constructLemma(), requis par LQRPpQpbetagamma *)
(* dans constructLemma(), requis par LPQRPpQpbetagamma *)
(* dans la couche 0 *)
Lemma LPQRPpQpOobetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQpOobetagamma requis par la preuve de (?)PQRPpQpOobetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQpOobetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpm2 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -1 et -2*)
assert(HPQRPpQpm3 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3).
{
	assert(HRpMtmp : rk(Rp :: nil) <= 1) by (solve_hyps_max HRpeq HRpM1).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) ((P :: Q :: R :: Pp :: Qp :: nil) ++ (Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_2 (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil) (nil) 4 0 1 HPQRPpQpRpmtmp Hmtmp HRpMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQpOobetagamma requis par la preuve de (?)PQRPpQpOobetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQpOobetagamma requis par la preuve de (?)PQRPpQpOobetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpOobetagammam2 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPQRPpQpOobetagammam3 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) >= 3).
{
	assert(HPQRPpQpmtmp : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3) by (solve_hyps_min HPQRPpQpeq HPQRPpQpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) 3 3 HPQRPpQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpOobetagammam4 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

assert(HPQRPpQpOobetagammaM : rk(P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRPpQpOobetagammam : rk(P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min HPQRPpQpOobetagammaeq HPQRPpQpOobetagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPQRPpQpbetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: beta :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQpbetagamma requis par la preuve de (?)PQRPpQpbetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQpbetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpm2 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -1 et -2*)
assert(HPQRPpQpm3 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3).
{
	assert(HRpMtmp : rk(Rp :: nil) <= 1) by (solve_hyps_max HRpeq HRpM1).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) ((P :: Q :: R :: Pp :: Qp :: nil) ++ (Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_2 (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil) (nil) 4 0 1 HPQRPpQpRpmtmp Hmtmp HRpMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQpbetagamma requis par la preuve de (?)PQRPpQpbetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQpbetagamma requis par la preuve de (?)PQRPpQpbetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpbetagammam2 : rk(P :: Q :: R :: Pp :: Qp :: beta :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPQRPpQpbetagammam3 : rk(P :: Q :: R :: Pp :: Qp :: beta :: gamma :: nil) >= 3).
{
	assert(HPQRPpQpmtmp : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3) by (solve_hyps_min HPQRPpQpeq HPQRPpQpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: beta :: gamma :: nil) 3 3 HPQRPpQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 -4 et -4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma ::  de rang :  4 et 4 	 AiB : P :: Pp ::  de rang :  2 et 2 	 A : P :: Pp :: Oo ::   de rang : 2 et 2 *)
assert(HPQRPpQpbetagammam4 : rk(P :: Q :: R :: Pp :: Qp :: beta :: gamma :: nil) >= 4).
{
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	assert(HPQRPpQpOobetagammaeq : rk(P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) = 4) by (apply LPQRPpQpOobetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQRPpQpOobetagammamtmp : rk(P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPQRPpQpOobetagammaeq HPQRPpQpOobetagammam4).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hincl : incl (P :: Pp :: nil) (list_inter (P :: Pp :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) (P :: Pp :: Oo :: P :: Q :: R :: Pp :: Qp :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Oo :: P :: Q :: R :: Pp :: Qp :: beta :: gamma :: nil) ((P :: Pp :: Oo :: nil) ++ (P :: Q :: R :: Pp :: Qp :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpOobetagammamtmp;try rewrite HT2 in HPQRPpQpOobetagammamtmp.
	assert(HT := rule_4 (P :: Pp :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: beta :: gamma :: nil) (P :: Pp :: nil) 4 2 2 HPQRPpQpOobetagammamtmp HPPpmtmp HPPpOoMtmp Hincl); apply HT.
}

assert(HPQRPpQpbetagammaM : rk(P :: Q :: R :: Pp :: Qp :: beta :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRPpQpbetagammam : rk(P :: Q :: R :: Pp :: Qp :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min HPQRPpQpbetagammaeq HPQRPpQpbetagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LQRPpQpbetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(Q :: R :: Pp :: Qp :: beta :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour QRPpQpbetagamma requis par la preuve de (?)QRPpQpbetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour QRPpQpbetagamma requis par la preuve de (?)QRPpQpbetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour QRPpQpbetagamma requis par la preuve de (?)QRPpQpbetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HQRPpQpbetagammam2 : rk(Q :: R :: Pp :: Qp :: beta :: gamma :: nil) >= 2).
{
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Q :: Qp :: nil) (Q :: R :: Pp :: Qp :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: Qp :: nil) (Q :: R :: Pp :: Qp :: beta :: gamma :: nil) 2 2 HQQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 4 -2 et -4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma ::  de rang :  4 et 4 	 AiB : Pp ::  de rang :  1 et 1 	 A : P :: Pp :: Oo ::   de rang : 2 et 2 *)
assert(HQRPpQpbetagammam3 : rk(Q :: R :: Pp :: Qp :: beta :: gamma :: nil) >= 3).
{
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	assert(HPQRPpQpOobetagammaeq : rk(P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) = 4) by (apply LPQRPpQpOobetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQRPpQpOobetagammamtmp : rk(P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPQRPpQpOobetagammaeq HPQRPpQpOobetagammam4).
	assert(HPpmtmp : rk(Pp :: nil) >= 1) by (solve_hyps_min HPpeq HPpm1).
	assert(Hincl : incl (Pp :: nil) (list_inter (P :: Pp :: Oo :: nil) (Q :: R :: Pp :: Qp :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) (P :: Pp :: Oo :: Q :: R :: Pp :: Qp :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Oo :: Q :: R :: Pp :: Qp :: beta :: gamma :: nil) ((P :: Pp :: Oo :: nil) ++ (Q :: R :: Pp :: Qp :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpOobetagammamtmp;try rewrite HT2 in HPQRPpQpOobetagammamtmp.
	assert(HT := rule_4 (P :: Pp :: Oo :: nil) (Q :: R :: Pp :: Qp :: beta :: gamma :: nil) (Pp :: nil) 4 1 2 HPQRPpQpOobetagammamtmp HPpmtmp HPPpOoMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et -4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: beta :: gamma ::  de rang :  4 et 4 	 AiB : Q :: beta ::  de rang :  2 et 2 	 A : P :: Q :: beta ::   de rang : 2 et 2 *)
assert(HQRPpQpbetagammam4 : rk(Q :: R :: Pp :: Qp :: beta :: gamma :: nil) >= 4).
{
	assert(HPQbetaMtmp : rk(P :: Q :: beta :: nil) <= 2) by (solve_hyps_max HPQbetaeq HPQbetaM2).
	assert(HPQRPpQpbetagammaeq : rk(P :: Q :: R :: Pp :: Qp :: beta :: gamma :: nil) = 4) by (apply LPQRPpQpbetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQRPpQpbetagammamtmp : rk(P :: Q :: R :: Pp :: Qp :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPQRPpQpbetagammaeq HPQRPpQpbetagammam4).
	assert(HQbetaeq : rk(Q :: beta :: nil) = 2) by (apply LQbeta with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HQbetamtmp : rk(Q :: beta :: nil) >= 2) by (solve_hyps_min HQbetaeq HQbetam2).
	assert(Hincl : incl (Q :: beta :: nil) (list_inter (P :: Q :: beta :: nil) (Q :: R :: Pp :: Qp :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: beta :: gamma :: nil) (P :: Q :: beta :: Q :: R :: Pp :: Qp :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: beta :: Q :: R :: Pp :: Qp :: beta :: gamma :: nil) ((P :: Q :: beta :: nil) ++ (Q :: R :: Pp :: Qp :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpbetagammamtmp;try rewrite HT2 in HPQRPpQpbetagammamtmp.
	assert(HT := rule_4 (P :: Q :: beta :: nil) (Q :: R :: Pp :: Qp :: beta :: gamma :: nil) (Q :: beta :: nil) 4 2 2 HPQRPpQpbetagammamtmp HQbetamtmp HPQbetaMtmp Hincl); apply HT.
}

assert(HQRPpQpbetagammaM : rk(Q :: R :: Pp :: Qp :: beta :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HQRPpQpbetagammam : rk(Q :: R :: Pp :: Qp :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min HQRPpQpbetagammaeq HQRPpQpbetagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPpQpbetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(Pp :: Qp :: beta :: gamma ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PpQpbetagamma requis par la preuve de (?)PpQpbetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PpQpbetagamma requis par la preuve de (?)PpQpbetagamma pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PpQpRpalphabetagamma requis par la preuve de (?)PpQpbetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PpQpRpalphabetagamma requis par la preuve de (?)PpQpRpalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRPpQpRpalphabetagamma requis par la preuve de (?)PpQpRpalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRPpQpRp requis par la preuve de (?)PRPpQpRpalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour QPp requis par la preuve de (?)PRPpQpRp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpQpRp requis par la preuve de (?)PRPpQpRp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpQpRp requis par la preuve de (?)PRPpQpRp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPRPpQpRpm2 : rk(P :: R :: Pp :: Qp :: Rp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: -4 -2 et 5*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Rp ::  de rang :  4 et 4 	 AiB : Pp ::  de rang :  1 et 1 	 A : Q :: Pp ::   de rang : 1 et 2 *)
assert(HPRPpQpRpm3 : rk(P :: R :: Pp :: Qp :: Rp :: nil) >= 3).
{
	assert(HQPpMtmp : rk(Q :: Pp :: nil) <= 2) by (solve_hyps_max HQPpeq HQPpM2).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(HPpmtmp : rk(Pp :: nil) >= 1) by (solve_hyps_min HPpeq HPpm1).
	assert(Hincl : incl (Pp :: nil) (list_inter (Q :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (Q :: Pp :: P :: R :: Pp :: Qp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Pp :: P :: R :: Pp :: Qp :: Rp :: nil) ((Q :: Pp :: nil) ++ (P :: R :: Pp :: Qp :: Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_4 (Q :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: nil) (Pp :: nil) 4 1 2 HPQRPpQpRpmtmp HPpmtmp HQPpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpQpRpalphabetagamma requis par la preuve de (?)PRPpQpRpalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpQpRpalphabetagamma requis par la preuve de (?)PRPpQpRpalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPRPpQpRpalphabetagammam2 : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPRPpQpRpalphabetagammam3 : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 3).
{
	assert(HPRPpQpRpmtmp : rk(P :: R :: Pp :: Qp :: Rp :: nil) >= 3) by (solve_hyps_min HPRPpQpRpeq HPRPpQpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: R :: Pp :: Qp :: Rp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: R :: Pp :: Qp :: Rp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) 3 3 HPRPpQpRpmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PpQpRpalphabetagamma requis par la preuve de (?)PpQpRpalphabetagamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma ::  de rang :  3 et 4 	 AiB : alpha ::  de rang :  1 et 1 	 A : P :: R :: alpha ::   de rang : 2 et 2 *)
assert(HPpQpRpalphabetagammam2 : rk(Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 2).
{
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	assert(HPRPpQpRpalphabetagammamtmp : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 3) by (solve_hyps_min HPRPpQpRpalphabetagammaeq HPRPpQpRpalphabetagammam3).
	assert(Halphamtmp : rk(alpha :: nil) >= 1) by (solve_hyps_min Halphaeq Halpham1).
	assert(Hincl : incl (alpha :: nil) (list_inter (P :: R :: alpha :: nil) (Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) (P :: R :: alpha :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: alpha :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) ((P :: R :: alpha :: nil) ++ (Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPRPpQpRpalphabetagammamtmp;try rewrite HT2 in HPRPpQpRpalphabetagammamtmp.
	assert(HT := rule_4 (P :: R :: alpha :: nil) (Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) (alpha :: nil) 3 1 2 HPRPpQpRpalphabetagammamtmp Halphamtmp HPRalphaMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPpQpRpalphabetagammam3 : rk(Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 3).
{
	assert(HPpQpalphaeq : rk(Pp :: Qp :: alpha :: nil) = 3) by (apply LPpQpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpQpalphamtmp : rk(Pp :: Qp :: alpha :: nil) >= 3) by (solve_hyps_min HPpQpalphaeq HPpQpalpham3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: alpha :: nil) (Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: alpha :: nil) (Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) 3 3 HPpQpalphamtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PpQpbetagamma requis par la preuve de (?)PpQpbetagamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : Pp :: Qp :: Rp :: alpha :: beta :: gamma ::  de rang :  3 et 4 	 AiB : Pp ::  de rang :  1 et 1 	 A : Pp :: Rp :: alpha ::   de rang : 2 et 2 *)
assert(HPpQpbetagammam2 : rk(Pp :: Qp :: beta :: gamma :: nil) >= 2).
{
	assert(HPpRpalphaMtmp : rk(Pp :: Rp :: alpha :: nil) <= 2) by (solve_hyps_max HPpRpalphaeq HPpRpalphaM2).
	assert(HPpQpRpalphabetagammamtmp : rk(Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 3) by (solve_hyps_min HPpQpRpalphabetagammaeq HPpQpRpalphabetagammam3).
	assert(HPpmtmp : rk(Pp :: nil) >= 1) by (solve_hyps_min HPpeq HPpm1).
	assert(Hincl : incl (Pp :: nil) (list_inter (Pp :: Rp :: alpha :: nil) (Pp :: Qp :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) (Pp :: Rp :: alpha :: Pp :: Qp :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: Rp :: alpha :: Pp :: Qp :: beta :: gamma :: nil) ((Pp :: Rp :: alpha :: nil) ++ (Pp :: Qp :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPpQpRpalphabetagammamtmp;try rewrite HT2 in HPpQpRpalphabetagammamtmp.
	assert(HT := rule_4 (Pp :: Rp :: alpha :: nil) (Pp :: Qp :: beta :: gamma :: nil) (Pp :: nil) 3 1 2 HPpQpRpalphabetagammamtmp HPpmtmp HPpRpalphaMtmp Hincl); apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -2 et 5*)
assert(HPpQpbetagammaM3 : rk(Pp :: Qp :: beta :: gamma :: nil) <= 3).
{
	assert(HPpQpbetaMtmp : rk(Pp :: Qp :: beta :: nil) <= 2) by (solve_hyps_max HPpQpbetaeq HPpQpbetaM2).
	assert(HgammaMtmp : rk(gamma :: nil) <= 1) by (solve_hyps_max Hgammaeq HgammaM1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Pp :: Qp :: beta :: nil) (gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Pp :: Qp :: beta :: gamma :: nil) (Pp :: Qp :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: Qp :: beta :: gamma :: nil) ((Pp :: Qp :: beta :: nil) ++ (gamma :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Pp :: Qp :: beta :: nil) (gamma :: nil) (nil) 2 1 0 HPpQpbetaMtmp HgammaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 -2 et -4*)
(* ensembles concernés AUB : Q :: R :: Pp :: Qp :: beta :: gamma ::  de rang :  4 et 4 	 AiB : gamma ::  de rang :  1 et 1 	 A : Q :: R :: gamma ::   de rang : 2 et 2 *)
assert(HPpQpbetagammam3 : rk(Pp :: Qp :: beta :: gamma :: nil) >= 3).
{
	assert(HQRgammaMtmp : rk(Q :: R :: gamma :: nil) <= 2) by (solve_hyps_max HQRgammaeq HQRgammaM2).
	assert(HQRPpQpbetagammaeq : rk(Q :: R :: Pp :: Qp :: beta :: gamma :: nil) = 4) by (apply LQRPpQpbetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HQRPpQpbetagammamtmp : rk(Q :: R :: Pp :: Qp :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HQRPpQpbetagammaeq HQRPpQpbetagammam4).
	assert(Hgammamtmp : rk(gamma :: nil) >= 1) by (solve_hyps_min Hgammaeq Hgammam1).
	assert(Hincl : incl (gamma :: nil) (list_inter (Q :: R :: gamma :: nil) (Pp :: Qp :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Q :: R :: Pp :: Qp :: beta :: gamma :: nil) (Q :: R :: gamma :: Pp :: Qp :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: R :: gamma :: Pp :: Qp :: beta :: gamma :: nil) ((Q :: R :: gamma :: nil) ++ (Pp :: Qp :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HQRPpQpbetagammamtmp;try rewrite HT2 in HQRPpQpbetagammamtmp.
	assert(HT := rule_4 (Q :: R :: gamma :: nil) (Pp :: Qp :: beta :: gamma :: nil) (gamma :: nil) 4 1 2 HQRPpQpbetagammamtmp Hgammamtmp HQRgammaMtmp Hincl); apply HT.
}

assert(HPpQpbetagammaM : rk(Pp :: Qp :: beta :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPpQpbetagammam : rk(Pp :: Qp :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min HPpQpbetagammaeq HPpQpbetagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPQRPpOobetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Oo :: beta :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpOobetagamma requis par la preuve de (?)PQRPpOobetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpOobetagamma requis par la preuve de (?)PQRPpOobetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpOobetagammam2 : rk(P :: Q :: R :: Pp :: Oo :: beta :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Oo :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Oo :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpOobetagammam4 : rk(P :: Q :: R :: Pp :: Oo :: beta :: gamma :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Oo :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Oo :: beta :: gamma :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

assert(HPQRPpOobetagammaM : rk(P :: Q :: R :: Pp :: Oo :: beta :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRPpOobetagammam : rk(P :: Q :: R :: Pp :: Oo :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min HPQRPpOobetagammaeq HPQRPpOobetagammam1).
intuition.
Qed.

(* dans constructLemma(), requis par LPalphabetagamma *)
(* dans la couche 0 *)
Lemma LPQalphabetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Q :: alpha :: beta :: gamma ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQalphabetagamma requis par la preuve de (?)PQalphabetagamma pour la règle 1  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour PQPpQpalphabetagamma requis par la preuve de (?)PQalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour PQPpQpRpalphabetagamma requis par la preuve de (?)PQPpQpalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQPpQpRpalphabetagamma requis par la preuve de (?)PQPpQpRpalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQPpQpRp requis par la preuve de (?)PQPpQpRpalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour RPp requis par la preuve de (?)PQPpQpRp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQPpQpRp requis par la preuve de (?)PQPpQpRp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQPpQpRp requis par la preuve de (?)PQPpQpRp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQPpQpRpm2 : rk(P :: Q :: Pp :: Qp :: Rp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: Pp :: Qp :: Rp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: Pp :: Qp :: Rp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: -4 -2 et 5*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Rp ::  de rang :  4 et 4 	 AiB : Pp ::  de rang :  1 et 1 	 A : R :: Pp ::   de rang : 1 et 2 *)
assert(HPQPpQpRpm3 : rk(P :: Q :: Pp :: Qp :: Rp :: nil) >= 3).
{
	assert(HRPpMtmp : rk(R :: Pp :: nil) <= 2) by (solve_hyps_max HRPpeq HRPpM2).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(HPpmtmp : rk(Pp :: nil) >= 1) by (solve_hyps_min HPpeq HPpm1).
	assert(Hincl : incl (Pp :: nil) (list_inter (R :: Pp :: nil) (P :: Q :: Pp :: Qp :: Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (R :: Pp :: P :: Q :: Pp :: Qp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (R :: Pp :: P :: Q :: Pp :: Qp :: Rp :: nil) ((R :: Pp :: nil) ++ (P :: Q :: Pp :: Qp :: Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_4 (R :: Pp :: nil) (P :: Q :: Pp :: Qp :: Rp :: nil) (Pp :: nil) 4 1 2 HPQRPpQpRpmtmp HPpmtmp HRPpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQPpQpRpalphabetagamma requis par la preuve de (?)PQPpQpRpalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQPpQpRpalphabetagamma requis par la preuve de (?)PQPpQpRpalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQPpQpRpalphabetagammam2 : rk(P :: Q :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPQPpQpRpalphabetagammam3 : rk(P :: Q :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 3).
{
	assert(HPQPpQpRpmtmp : rk(P :: Q :: Pp :: Qp :: Rp :: nil) >= 3) by (solve_hyps_min HPQPpQpRpeq HPQPpQpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: Pp :: Qp :: Rp :: nil) (P :: Q :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: Pp :: Qp :: Rp :: nil) (P :: Q :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) 3 3 HPQPpQpRpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQPpQpRpalphabetagammam4 : rk(P :: Q :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 4).
{
	assert(HPQPpRpalphaeq : rk(P :: Q :: Pp :: Rp :: alpha :: nil) = 4) by (apply LPQPpRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQPpRpalphamtmp : rk(P :: Q :: Pp :: Rp :: alpha :: nil) >= 4) by (solve_hyps_min HPQPpRpalphaeq HPQPpRpalpham4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: Pp :: Rp :: alpha :: nil) (P :: Q :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: Pp :: Rp :: alpha :: nil) (P :: Q :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) 4 4 HPQPpRpalphamtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQPpQpalphabetagamma requis par la preuve de (?)PQPpQpalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour PQRPpQpOoalphabetagamma requis par la preuve de (?)PQPpQpalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQpOoalphabetagamma requis par la preuve de (?)PQRPpQpOoalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQpOoalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpm2 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -1 et -2*)
assert(HPQRPpQpm3 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3).
{
	assert(HRpMtmp : rk(Rp :: nil) <= 1) by (solve_hyps_max HRpeq HRpM1).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) ((P :: Q :: R :: Pp :: Qp :: nil) ++ (Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_2 (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil) (nil) 4 0 1 HPQRPpQpRpmtmp Hmtmp HRpMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQpOoalphabetagamma requis par la preuve de (?)PQRPpQpOoalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQpOoalphabetagamma requis par la preuve de (?)PQRPpQpOoalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpOoalphabetagammam2 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPQRPpQpOoalphabetagammam3 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 3).
{
	assert(HPQRPpQpmtmp : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3) by (solve_hyps_min HPQRPpQpeq HPQRPpQpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) 3 3 HPQRPpQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpOoalphabetagammam4 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQPpQpalphabetagamma requis par la preuve de (?)PQPpQpalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQPpQpalphabetagamma requis par la preuve de (?)PQPpQpalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQPpQpalphabetagammam2 : rk(P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma ::  de rang :  4 et 4 	 AiB : P :: Pp ::  de rang :  2 et 2 	 A : P :: R :: Pp :: Oo ::   de rang : 3 et 3 *)
assert(HPQPpQpalphabetagammam3 : rk(P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 3).
{
	assert(HPRPpOoeq : rk(P :: R :: Pp :: Oo :: nil) = 3) by (apply LPRPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPRPpOoMtmp : rk(P :: R :: Pp :: Oo :: nil) <= 3) by (solve_hyps_max HPRPpOoeq HPRPpOoM3).
	assert(HPQRPpQpOoalphabetagammamtmp : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPQRPpQpOoalphabetagammaeq HPQRPpQpOoalphabetagammam4).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hincl : incl (P :: Pp :: nil) (list_inter (P :: R :: Pp :: Oo :: nil) (P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) (P :: R :: Pp :: Oo :: P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: Pp :: Oo :: P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil) ((P :: R :: Pp :: Oo :: nil) ++ (P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpOoalphabetagammamtmp;try rewrite HT2 in HPQRPpQpOoalphabetagammamtmp.
	assert(HT := rule_4 (P :: R :: Pp :: Oo :: nil) (P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil) (P :: Pp :: nil) 4 2 3 HPQRPpQpOoalphabetagammamtmp HPPpmtmp HPRPpOoMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : P :: Q :: Pp :: Qp :: Rp :: alpha :: beta :: gamma ::  de rang :  4 et 4 	 AiB : Pp :: Qp :: alpha ::  de rang :  3 et 3 	 A : Pp :: Qp :: Rp :: alpha ::   de rang : 3 et 3 *)
assert(HPQPpQpalphabetagammam4 : rk(P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 4).
{
	assert(HPpQpRpalphaeq : rk(Pp :: Qp :: Rp :: alpha :: nil) = 3) by (apply LPpQpRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpQpRpalphaMtmp : rk(Pp :: Qp :: Rp :: alpha :: nil) <= 3) by (solve_hyps_max HPpQpRpalphaeq HPpQpRpalphaM3).
	assert(HPQPpQpRpalphabetagammamtmp : rk(P :: Q :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPQPpQpRpalphabetagammaeq HPQPpQpRpalphabetagammam4).
	assert(HPpQpalphaeq : rk(Pp :: Qp :: alpha :: nil) = 3) by (apply LPpQpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpQpalphamtmp : rk(Pp :: Qp :: alpha :: nil) >= 3) by (solve_hyps_min HPpQpalphaeq HPpQpalpham3).
	assert(Hincl : incl (Pp :: Qp :: alpha :: nil) (list_inter (Pp :: Qp :: Rp :: alpha :: nil) (P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) (Pp :: Qp :: Rp :: alpha :: P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: Qp :: Rp :: alpha :: P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil) ((Pp :: Qp :: Rp :: alpha :: nil) ++ (P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQPpQpRpalphabetagammamtmp;try rewrite HT2 in HPQPpQpRpalphabetagammamtmp.
	assert(HT := rule_4 (Pp :: Qp :: Rp :: alpha :: nil) (P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil) (Pp :: Qp :: alpha :: nil) 4 3 3 HPQPpQpRpalphabetagammamtmp HPpQpalphamtmp HPpQpRpalphaMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQalphabetagamma requis par la preuve de (?)PQalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour PQRPpOoalphabetagamma requis par la preuve de (?)PQalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpOoalphabetagamma requis par la preuve de (?)PQRPpOoalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpOoalphabetagamma requis par la preuve de (?)PQRPpOoalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpOoalphabetagammam2 : rk(P :: Q :: R :: Pp :: Oo :: alpha :: beta :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Oo :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpOoalphabetagammam4 : rk(P :: Q :: R :: Pp :: Oo :: alpha :: beta :: gamma :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Oo :: alpha :: beta :: gamma :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQalphabetagamma requis par la preuve de (?)PQalphabetagamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Oo :: alpha :: beta :: gamma ::  de rang :  4 et 4 	 AiB : P ::  de rang :  1 et 1 	 A : P :: R :: Pp :: Oo ::   de rang : 3 et 3 *)
assert(HPQalphabetagammam2 : rk(P :: Q :: alpha :: beta :: gamma :: nil) >= 2).
{
	assert(HPRPpOoeq : rk(P :: R :: Pp :: Oo :: nil) = 3) by (apply LPRPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPRPpOoMtmp : rk(P :: R :: Pp :: Oo :: nil) <= 3) by (solve_hyps_max HPRPpOoeq HPRPpOoM3).
	assert(HPQRPpOoalphabetagammamtmp : rk(P :: Q :: R :: Pp :: Oo :: alpha :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPQRPpOoalphabetagammaeq HPQRPpOoalphabetagammam4).
	assert(HPmtmp : rk(P :: nil) >= 1) by (solve_hyps_min HPeq HPm1).
	assert(Hincl : incl (P :: nil) (list_inter (P :: R :: Pp :: Oo :: nil) (P :: Q :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Oo :: alpha :: beta :: gamma :: nil) (P :: R :: Pp :: Oo :: P :: Q :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: Pp :: Oo :: P :: Q :: alpha :: beta :: gamma :: nil) ((P :: R :: Pp :: Oo :: nil) ++ (P :: Q :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpOoalphabetagammamtmp;try rewrite HT2 in HPQRPpOoalphabetagammamtmp.
	assert(HT := rule_4 (P :: R :: Pp :: Oo :: nil) (P :: Q :: alpha :: beta :: gamma :: nil) (P :: nil) 4 1 3 HPQRPpOoalphabetagammamtmp HPmtmp HPRPpOoMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : P :: Q :: Pp :: Qp :: alpha :: beta :: gamma ::  de rang :  4 et 4 	 AiB : beta ::  de rang :  1 et 1 	 A : Pp :: Qp :: beta ::   de rang : 2 et 2 *)
assert(HPQalphabetagammam3 : rk(P :: Q :: alpha :: beta :: gamma :: nil) >= 3).
{
	assert(HPpQpbetaMtmp : rk(Pp :: Qp :: beta :: nil) <= 2) by (solve_hyps_max HPpQpbetaeq HPpQpbetaM2).
	assert(HPQPpQpalphabetagammamtmp : rk(P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPQPpQpalphabetagammaeq HPQPpQpalphabetagammam4).
	assert(Hbetamtmp : rk(beta :: nil) >= 1) by (solve_hyps_min Hbetaeq Hbetam1).
	assert(Hincl : incl (beta :: nil) (list_inter (Pp :: Qp :: beta :: nil) (P :: Q :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil) (Pp :: Qp :: beta :: P :: Q :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: Qp :: beta :: P :: Q :: alpha :: beta :: gamma :: nil) ((Pp :: Qp :: beta :: nil) ++ (P :: Q :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQPpQpalphabetagammamtmp;try rewrite HT2 in HPQPpQpalphabetagammamtmp.
	assert(HT := rule_4 (Pp :: Qp :: beta :: nil) (P :: Q :: alpha :: beta :: gamma :: nil) (beta :: nil) 4 1 2 HPQPpQpalphabetagammamtmp Hbetamtmp HPpQpbetaMtmp Hincl); apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HPQalphabetagammaM3 : rk(P :: Q :: alpha :: beta :: gamma :: nil) <= 3).
{
	assert(HPQalphagammaeq : rk(P :: Q :: alpha :: gamma :: nil) = 3) by (apply LPQalphagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQalphagammaMtmp : rk(P :: Q :: alpha :: gamma :: nil) <= 3) by (solve_hyps_max HPQalphagammaeq HPQalphagammaM3).
	assert(HPQbetagammaeq : rk(P :: Q :: beta :: gamma :: nil) = 3) by (apply LPQbetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQbetagammaMtmp : rk(P :: Q :: beta :: gamma :: nil) <= 3) by (solve_hyps_max HPQbetagammaeq HPQbetagammaM3).
	assert(HPQgammaeq : rk(P :: Q :: gamma :: nil) = 3) by (apply LPQgamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQgammamtmp : rk(P :: Q :: gamma :: nil) >= 3) by (solve_hyps_min HPQgammaeq HPQgammam3).
	assert(Hincl : incl (P :: Q :: gamma :: nil) (list_inter (P :: Q :: alpha :: gamma :: nil) (P :: Q :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: alpha :: beta :: gamma :: nil) (P :: Q :: alpha :: gamma :: P :: Q :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: alpha :: gamma :: P :: Q :: beta :: gamma :: nil) ((P :: Q :: alpha :: gamma :: nil) ++ (P :: Q :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P :: Q :: alpha :: gamma :: nil) (P :: Q :: beta :: gamma :: nil) (P :: Q :: gamma :: nil) 3 3 3 HPQalphagammaMtmp HPQbetagammaMtmp HPQgammamtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HPQalphabetagammaM : rk(P :: Q :: alpha :: beta :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQalphabetagammam : rk(P :: Q :: alpha :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min HPQalphabetagammaeq HPQalphabetagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPalphabetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: alpha :: beta :: gamma ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour Palphabetagamma requis par la preuve de (?)Palphabetagamma pour la règle 6  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour PPpQpalphabetagamma requis par la preuve de (?)Palphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour PPpQpRpalphabetagamma requis par la preuve de (?)PPpQpalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour PRPpQpRpalphabetagamma requis par la preuve de (?)PPpQpRpalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRPpQpRpalphabetagamma requis par la preuve de (?)PRPpQpRpalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRPpQpRp requis par la preuve de (?)PRPpQpRpalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour QPp requis par la preuve de (?)PRPpQpRp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpQpRp requis par la preuve de (?)PRPpQpRp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpQpRp requis par la preuve de (?)PRPpQpRp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPRPpQpRpm2 : rk(P :: R :: Pp :: Qp :: Rp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: -4 -2 et 5*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Rp ::  de rang :  4 et 4 	 AiB : Pp ::  de rang :  1 et 1 	 A : Q :: Pp ::   de rang : 1 et 2 *)
assert(HPRPpQpRpm3 : rk(P :: R :: Pp :: Qp :: Rp :: nil) >= 3).
{
	assert(HQPpMtmp : rk(Q :: Pp :: nil) <= 2) by (solve_hyps_max HQPpeq HQPpM2).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(HPpmtmp : rk(Pp :: nil) >= 1) by (solve_hyps_min HPpeq HPpm1).
	assert(Hincl : incl (Pp :: nil) (list_inter (Q :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (Q :: Pp :: P :: R :: Pp :: Qp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Pp :: P :: R :: Pp :: Qp :: Rp :: nil) ((Q :: Pp :: nil) ++ (P :: R :: Pp :: Qp :: Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_4 (Q :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: nil) (Pp :: nil) 4 1 2 HPQRPpQpRpmtmp HPpmtmp HQPpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpQpRpalphabetagamma requis par la preuve de (?)PRPpQpRpalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpQpRpalphabetagamma requis par la preuve de (?)PRPpQpRpalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPRPpQpRpalphabetagammam2 : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPRPpQpRpalphabetagammam3 : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 3).
{
	assert(HPRPpQpRpmtmp : rk(P :: R :: Pp :: Qp :: Rp :: nil) >= 3) by (solve_hyps_min HPRPpQpRpeq HPRPpQpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: R :: Pp :: Qp :: Rp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: R :: Pp :: Qp :: Rp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) 3 3 HPRPpQpRpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPRPpQpRpalphabetagammam4 : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 4).
{
	assert(HPRPpQpalphaeq : rk(P :: R :: Pp :: Qp :: alpha :: nil) = 4) by (apply LPRPpQpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPRPpQpalphamtmp : rk(P :: R :: Pp :: Qp :: alpha :: nil) >= 4) by (solve_hyps_min HPRPpQpalphaeq HPRPpQpalpham4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: R :: Pp :: Qp :: alpha :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: R :: Pp :: Qp :: alpha :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) 4 4 HPRPpQpalphamtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PPpQpRpalphabetagamma requis par la preuve de (?)PPpQpRpalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PPpQpRpalphabetagamma requis par la preuve de (?)PPpQpRpalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PPpQpRpalphabetagamma requis par la preuve de (?)PPpQpRpalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPPpQpRpalphabetagammam2 : rk(P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPPpQpRpalphabetagammam3 : rk(P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 3).
{
	assert(HPpQpalphaeq : rk(Pp :: Qp :: alpha :: nil) = 3) by (apply LPpQpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpQpalphamtmp : rk(Pp :: Qp :: alpha :: nil) >= 3) by (solve_hyps_min HPpQpalphaeq HPpQpalpham3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: alpha :: nil) (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: alpha :: nil) (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) 3 3 HPpQpalphamtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma ::  de rang :  4 et 4 	 AiB : P :: Pp :: Rp :: alpha ::  de rang :  3 et 3 	 A : P :: R :: Pp :: Rp :: alpha ::   de rang : 3 et 3 *)
assert(HPPpQpRpalphabetagammam4 : rk(P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 4).
{
	assert(HPRPpRpalphaeq : rk(P :: R :: Pp :: Rp :: alpha :: nil) = 3) by (apply LPRPpRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPRPpRpalphaMtmp : rk(P :: R :: Pp :: Rp :: alpha :: nil) <= 3) by (solve_hyps_max HPRPpRpalphaeq HPRPpRpalphaM3).
	assert(HPRPpQpRpalphabetagammamtmp : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPRPpQpRpalphabetagammaeq HPRPpQpRpalphabetagammam4).
	assert(HPPpRpalphaeq : rk(P :: Pp :: Rp :: alpha :: nil) = 3) by (apply LPPpRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPPpRpalphamtmp : rk(P :: Pp :: Rp :: alpha :: nil) >= 3) by (solve_hyps_min HPPpRpalphaeq HPPpRpalpham3).
	assert(Hincl : incl (P :: Pp :: Rp :: alpha :: nil) (list_inter (P :: R :: Pp :: Rp :: alpha :: nil) (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) (P :: R :: Pp :: Rp :: alpha :: P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: Pp :: Rp :: alpha :: P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) ((P :: R :: Pp :: Rp :: alpha :: nil) ++ (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPRPpQpRpalphabetagammamtmp;try rewrite HT2 in HPRPpQpRpalphabetagammamtmp.
	assert(HT := rule_4 (P :: R :: Pp :: Rp :: alpha :: nil) (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) (P :: Pp :: Rp :: alpha :: nil) 4 3 3 HPRPpQpRpalphabetagammamtmp HPPpRpalphamtmp HPRPpRpalphaMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PPpQpalphabetagamma requis par la preuve de (?)PPpQpalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PPpQpalphabetagamma requis par la preuve de (?)PPpQpalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PPpQpalphabetagamma requis par la preuve de (?)PPpQpalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPPpQpalphabetagammam2 : rk(P :: Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Pp :: Qp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Pp :: Qp :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPPpQpalphabetagammam3 : rk(P :: Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 3).
{
	assert(HPpQpalphaeq : rk(Pp :: Qp :: alpha :: nil) = 3) by (apply LPpQpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpQpalphamtmp : rk(Pp :: Qp :: alpha :: nil) >= 3) by (solve_hyps_min HPpQpalphaeq HPpQpalpham3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: alpha :: nil) (P :: Pp :: Qp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: alpha :: nil) (P :: Pp :: Qp :: alpha :: beta :: gamma :: nil) 3 3 HPpQpalphamtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma ::  de rang :  4 et 4 	 AiB : Pp :: Qp :: alpha ::  de rang :  3 et 3 	 A : Pp :: Qp :: Rp :: alpha ::   de rang : 3 et 3 *)
assert(HPPpQpalphabetagammam4 : rk(P :: Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 4).
{
	assert(HPpQpRpalphaeq : rk(Pp :: Qp :: Rp :: alpha :: nil) = 3) by (apply LPpQpRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpQpRpalphaMtmp : rk(Pp :: Qp :: Rp :: alpha :: nil) <= 3) by (solve_hyps_max HPpQpRpalphaeq HPpQpRpalphaM3).
	assert(HPPpQpRpalphabetagammamtmp : rk(P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPPpQpRpalphabetagammaeq HPPpQpRpalphabetagammam4).
	assert(HPpQpalphaeq : rk(Pp :: Qp :: alpha :: nil) = 3) by (apply LPpQpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpQpalphamtmp : rk(Pp :: Qp :: alpha :: nil) >= 3) by (solve_hyps_min HPpQpalphaeq HPpQpalpham3).
	assert(Hincl : incl (Pp :: Qp :: alpha :: nil) (list_inter (Pp :: Qp :: Rp :: alpha :: nil) (P :: Pp :: Qp :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) (Pp :: Qp :: Rp :: alpha :: P :: Pp :: Qp :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: Qp :: Rp :: alpha :: P :: Pp :: Qp :: alpha :: beta :: gamma :: nil) ((Pp :: Qp :: Rp :: alpha :: nil) ++ (P :: Pp :: Qp :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPPpQpRpalphabetagammamtmp;try rewrite HT2 in HPPpQpRpalphabetagammamtmp.
	assert(HT := rule_4 (Pp :: Qp :: Rp :: alpha :: nil) (P :: Pp :: Qp :: alpha :: beta :: gamma :: nil) (Pp :: Qp :: alpha :: nil) 4 3 3 HPPpQpRpalphabetagammamtmp HPpQpalphamtmp HPpQpRpalphaMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour Palphabetagamma requis par la preuve de (?)Palphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour Palphabetagamma requis par la preuve de (?)Palphabetagamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma ::  de rang :  4 et 4 	 AiB : alpha ::  de rang :  1 et 1 	 A : Pp :: Qp :: Rp :: alpha ::   de rang : 3 et 3 *)
assert(HPalphabetagammam2 : rk(P :: alpha :: beta :: gamma :: nil) >= 2).
{
	assert(HPpQpRpalphaeq : rk(Pp :: Qp :: Rp :: alpha :: nil) = 3) by (apply LPpQpRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpQpRpalphaMtmp : rk(Pp :: Qp :: Rp :: alpha :: nil) <= 3) by (solve_hyps_max HPpQpRpalphaeq HPpQpRpalphaM3).
	assert(HPPpQpRpalphabetagammamtmp : rk(P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPPpQpRpalphabetagammaeq HPPpQpRpalphabetagammam4).
	assert(Halphamtmp : rk(alpha :: nil) >= 1) by (solve_hyps_min Halphaeq Halpham1).
	assert(Hincl : incl (alpha :: nil) (list_inter (Pp :: Qp :: Rp :: alpha :: nil) (P :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) (Pp :: Qp :: Rp :: alpha :: P :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: Qp :: Rp :: alpha :: P :: alpha :: beta :: gamma :: nil) ((Pp :: Qp :: Rp :: alpha :: nil) ++ (P :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPPpQpRpalphabetagammamtmp;try rewrite HT2 in HPPpQpRpalphabetagammamtmp.
	assert(HT := rule_4 (Pp :: Qp :: Rp :: alpha :: nil) (P :: alpha :: beta :: gamma :: nil) (alpha :: nil) 4 1 3 HPPpQpRpalphabetagammamtmp Halphamtmp HPpQpRpalphaMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : P :: Pp :: Qp :: alpha :: beta :: gamma ::  de rang :  4 et 4 	 AiB : beta ::  de rang :  1 et 1 	 A : Pp :: Qp :: beta ::   de rang : 2 et 2 *)
assert(HPalphabetagammam3 : rk(P :: alpha :: beta :: gamma :: nil) >= 3).
{
	assert(HPpQpbetaMtmp : rk(Pp :: Qp :: beta :: nil) <= 2) by (solve_hyps_max HPpQpbetaeq HPpQpbetaM2).
	assert(HPPpQpalphabetagammamtmp : rk(P :: Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPPpQpalphabetagammaeq HPPpQpalphabetagammam4).
	assert(Hbetamtmp : rk(beta :: nil) >= 1) by (solve_hyps_min Hbetaeq Hbetam1).
	assert(Hincl : incl (beta :: nil) (list_inter (Pp :: Qp :: beta :: nil) (P :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Pp :: Qp :: alpha :: beta :: gamma :: nil) (Pp :: Qp :: beta :: P :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: Qp :: beta :: P :: alpha :: beta :: gamma :: nil) ((Pp :: Qp :: beta :: nil) ++ (P :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPPpQpalphabetagammamtmp;try rewrite HT2 in HPPpQpalphabetagammamtmp.
	assert(HT := rule_4 (Pp :: Qp :: beta :: nil) (P :: alpha :: beta :: gamma :: nil) (beta :: nil) 4 1 2 HPPpQpalphabetagammamtmp Hbetamtmp HPpQpbetaMtmp Hincl); apply HT.
}

(* Application de la règle 6 (code, 3 ou 4 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPalphabetagammaM3 : rk(P :: alpha :: beta :: gamma :: nil) <= 3).
{
	assert(HPQalphabetagammaeq : rk(P :: Q :: alpha :: beta :: gamma :: nil) = 3) by (apply LPQalphabetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQalphabetagammaMtmp : rk(P :: Q :: alpha :: beta :: gamma :: nil) <= 3) by (solve_hyps_max HPQalphabetagammaeq HPQalphabetagammaM3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: alpha :: beta :: gamma :: nil) (P :: Q :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P :: alpha :: beta :: gamma :: nil) (P :: Q :: alpha :: beta :: gamma :: nil) 3 3 HPQalphabetagammaMtmp Hcomp Hincl);apply HT.
}

assert(HPalphabetagammaM : rk(P :: alpha :: beta :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPalphabetagammam : rk(P :: alpha :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min HPalphabetagammaeq HPalphabetagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPpQpalphabetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(Pp :: Qp :: alpha :: beta :: gamma ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PpQpalphabetagamma requis par la preuve de (?)PpQpalphabetagamma pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PpQpalphabetagamma requis par la preuve de (?)PpQpalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRPpQpalphabetagamma requis par la preuve de (?)PpQpalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour PQRPpQpOoalphabetagamma requis par la preuve de (?)PRPpQpalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQpOoalphabetagamma requis par la preuve de (?)PQRPpQpOoalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQpOoalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpm2 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -1 et -2*)
assert(HPQRPpQpm3 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3).
{
	assert(HRpMtmp : rk(Rp :: nil) <= 1) by (solve_hyps_max HRpeq HRpM1).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) ((P :: Q :: R :: Pp :: Qp :: nil) ++ (Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_2 (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil) (nil) 4 0 1 HPQRPpQpRpmtmp Hmtmp HRpMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQpOoalphabetagamma requis par la preuve de (?)PQRPpQpOoalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQpOoalphabetagamma requis par la preuve de (?)PQRPpQpOoalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpOoalphabetagammam2 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPQRPpQpOoalphabetagammam3 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 3).
{
	assert(HPQRPpQpmtmp : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3) by (solve_hyps_min HPQRPpQpeq HPQRPpQpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) 3 3 HPQRPpQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpOoalphabetagammam4 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpQpalphabetagamma requis par la preuve de (?)PRPpQpalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpQpalphabetagamma requis par la preuve de (?)PRPpQpalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPRPpQpalphabetagammam2 : rk(P :: R :: Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Qp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Qp :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma ::  de rang :  4 et 4 	 AiB : P :: Pp ::  de rang :  2 et 2 	 A : P :: Q :: Pp :: Oo ::   de rang : 3 et 3 *)
assert(HPRPpQpalphabetagammam3 : rk(P :: R :: Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 3).
{
	assert(HPQPpOoeq : rk(P :: Q :: Pp :: Oo :: nil) = 3) by (apply LPQPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQPpOoMtmp : rk(P :: Q :: Pp :: Oo :: nil) <= 3) by (solve_hyps_max HPQPpOoeq HPQPpOoM3).
	assert(HPQRPpQpOoalphabetagammamtmp : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPQRPpQpOoalphabetagammaeq HPQRPpQpOoalphabetagammam4).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hincl : incl (P :: Pp :: nil) (list_inter (P :: Q :: Pp :: Oo :: nil) (P :: R :: Pp :: Qp :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) (P :: Q :: Pp :: Oo :: P :: R :: Pp :: Qp :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: Pp :: Oo :: P :: R :: Pp :: Qp :: alpha :: beta :: gamma :: nil) ((P :: Q :: Pp :: Oo :: nil) ++ (P :: R :: Pp :: Qp :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpOoalphabetagammamtmp;try rewrite HT2 in HPQRPpQpOoalphabetagammamtmp.
	assert(HT := rule_4 (P :: Q :: Pp :: Oo :: nil) (P :: R :: Pp :: Qp :: alpha :: beta :: gamma :: nil) (P :: Pp :: nil) 4 2 3 HPQRPpQpOoalphabetagammamtmp HPPpmtmp HPQPpOoMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PpQpalphabetagamma requis par la preuve de (?)PpQpalphabetagamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : P :: R :: Pp :: Qp :: alpha :: beta :: gamma ::  de rang :  3 et 4 	 AiB : alpha ::  de rang :  1 et 1 	 A : P :: R :: alpha ::   de rang : 2 et 2 *)
assert(HPpQpalphabetagammam2 : rk(Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 2).
{
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	assert(HPRPpQpalphabetagammamtmp : rk(P :: R :: Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 3) by (solve_hyps_min HPRPpQpalphabetagammaeq HPRPpQpalphabetagammam3).
	assert(Halphamtmp : rk(alpha :: nil) >= 1) by (solve_hyps_min Halphaeq Halpham1).
	assert(Hincl : incl (alpha :: nil) (list_inter (P :: R :: alpha :: nil) (Pp :: Qp :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: Qp :: alpha :: beta :: gamma :: nil) (P :: R :: alpha :: Pp :: Qp :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: alpha :: Pp :: Qp :: alpha :: beta :: gamma :: nil) ((P :: R :: alpha :: nil) ++ (Pp :: Qp :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPRPpQpalphabetagammamtmp;try rewrite HT2 in HPRPpQpalphabetagammamtmp.
	assert(HT := rule_4 (P :: R :: alpha :: nil) (Pp :: Qp :: alpha :: beta :: gamma :: nil) (alpha :: nil) 3 1 2 HPRPpQpalphabetagammamtmp Halphamtmp HPRalphaMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPpQpalphabetagammam3 : rk(Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 3).
{
	assert(HPpQpalphaeq : rk(Pp :: Qp :: alpha :: nil) = 3) by (apply LPpQpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpQpalphamtmp : rk(Pp :: Qp :: alpha :: nil) >= 3) by (solve_hyps_min HPpQpalphaeq HPpQpalpham3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: alpha :: nil) (Pp :: Qp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: alpha :: nil) (Pp :: Qp :: alpha :: beta :: gamma :: nil) 3 3 HPpQpalphamtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HPpQpalphabetagammaM3 : rk(Pp :: Qp :: alpha :: beta :: gamma :: nil) <= 3).
{
	assert(HPpQpalphagammaeq : rk(Pp :: Qp :: alpha :: gamma :: nil) = 3) by (apply LPpQpalphagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpQpalphagammaMtmp : rk(Pp :: Qp :: alpha :: gamma :: nil) <= 3) by (solve_hyps_max HPpQpalphagammaeq HPpQpalphagammaM3).
	assert(HPpQpbetagammaeq : rk(Pp :: Qp :: beta :: gamma :: nil) = 3) by (apply LPpQpbetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpQpbetagammaMtmp : rk(Pp :: Qp :: beta :: gamma :: nil) <= 3) by (solve_hyps_max HPpQpbetagammaeq HPpQpbetagammaM3).
	assert(HPpQpgammaeq : rk(Pp :: Qp :: gamma :: nil) = 3) by (apply LPpQpgamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpQpgammamtmp : rk(Pp :: Qp :: gamma :: nil) >= 3) by (solve_hyps_min HPpQpgammaeq HPpQpgammam3).
	assert(Hincl : incl (Pp :: Qp :: gamma :: nil) (list_inter (Pp :: Qp :: alpha :: gamma :: nil) (Pp :: Qp :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Pp :: Qp :: alpha :: beta :: gamma :: nil) (Pp :: Qp :: alpha :: gamma :: Pp :: Qp :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: Qp :: alpha :: gamma :: Pp :: Qp :: beta :: gamma :: nil) ((Pp :: Qp :: alpha :: gamma :: nil) ++ (Pp :: Qp :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Pp :: Qp :: alpha :: gamma :: nil) (Pp :: Qp :: beta :: gamma :: nil) (Pp :: Qp :: gamma :: nil) 3 3 3 HPpQpalphagammaMtmp HPpQpbetagammaMtmp HPpQpgammamtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HPpQpalphabetagammaM : rk(Pp :: Qp :: alpha :: beta :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPpQpalphabetagammam : rk(Pp :: Qp :: alpha :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min HPpQpalphabetagammaeq HPpQpalphabetagammam1).
intuition.
Qed.

(* dans constructLemma(), requis par LPPpQpalphabetagamma *)
(* dans constructLemma(), requis par LPPpQpRpalphabetagamma *)
(* dans la couche 0 *)
Lemma LPRPpQpRpalphabetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRPpQpRpalphabetagamma requis par la preuve de (?)PRPpQpRpalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRPpQpRp requis par la preuve de (?)PRPpQpRpalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour QPp requis par la preuve de (?)PRPpQpRp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpQpRp requis par la preuve de (?)PRPpQpRp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpQpRp requis par la preuve de (?)PRPpQpRp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPRPpQpRpm2 : rk(P :: R :: Pp :: Qp :: Rp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: -4 -2 et 5*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Rp ::  de rang :  4 et 4 	 AiB : Pp ::  de rang :  1 et 1 	 A : Q :: Pp ::   de rang : 1 et 2 *)
assert(HPRPpQpRpm3 : rk(P :: R :: Pp :: Qp :: Rp :: nil) >= 3).
{
	assert(HQPpMtmp : rk(Q :: Pp :: nil) <= 2) by (solve_hyps_max HQPpeq HQPpM2).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(HPpmtmp : rk(Pp :: nil) >= 1) by (solve_hyps_min HPpeq HPpm1).
	assert(Hincl : incl (Pp :: nil) (list_inter (Q :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (Q :: Pp :: P :: R :: Pp :: Qp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Pp :: P :: R :: Pp :: Qp :: Rp :: nil) ((Q :: Pp :: nil) ++ (P :: R :: Pp :: Qp :: Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_4 (Q :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: nil) (Pp :: nil) 4 1 2 HPQRPpQpRpmtmp HPpmtmp HQPpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpQpRpalphabetagamma requis par la preuve de (?)PRPpQpRpalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpQpRpalphabetagamma requis par la preuve de (?)PRPpQpRpalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPRPpQpRpalphabetagammam2 : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPRPpQpRpalphabetagammam3 : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 3).
{
	assert(HPRPpQpRpmtmp : rk(P :: R :: Pp :: Qp :: Rp :: nil) >= 3) by (solve_hyps_min HPRPpQpRpeq HPRPpQpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: R :: Pp :: Qp :: Rp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: R :: Pp :: Qp :: Rp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) 3 3 HPRPpQpRpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPRPpQpRpalphabetagammam4 : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 4).
{
	assert(HPRPpQpalphaeq : rk(P :: R :: Pp :: Qp :: alpha :: nil) = 4) by (apply LPRPpQpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPRPpQpalphamtmp : rk(P :: R :: Pp :: Qp :: alpha :: nil) >= 4) by (solve_hyps_min HPRPpQpalphaeq HPRPpQpalpham4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: R :: Pp :: Qp :: alpha :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: R :: Pp :: Qp :: alpha :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) 4 4 HPRPpQpalphamtmp Hcomp Hincl);apply HT.
}

assert(HPRPpQpRpalphabetagammaM : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPRPpQpRpalphabetagammam : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min HPRPpQpRpalphabetagammaeq HPRPpQpRpalphabetagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPPpQpRpalphabetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PPpQpRpalphabetagamma requis par la preuve de (?)PPpQpRpalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PPpQpRpalphabetagamma requis par la preuve de (?)PPpQpRpalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PPpQpRpalphabetagamma requis par la preuve de (?)PPpQpRpalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPPpQpRpalphabetagammam2 : rk(P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPPpQpRpalphabetagammam3 : rk(P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 3).
{
	assert(HPpQpalphaeq : rk(Pp :: Qp :: alpha :: nil) = 3) by (apply LPpQpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpQpalphamtmp : rk(Pp :: Qp :: alpha :: nil) >= 3) by (solve_hyps_min HPpQpalphaeq HPpQpalpham3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: alpha :: nil) (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: alpha :: nil) (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) 3 3 HPpQpalphamtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma ::  de rang :  4 et 4 	 AiB : P :: Pp :: Rp :: alpha ::  de rang :  3 et 3 	 A : P :: R :: Pp :: Rp :: alpha ::   de rang : 3 et 3 *)
assert(HPPpQpRpalphabetagammam4 : rk(P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 4).
{
	assert(HPRPpRpalphaeq : rk(P :: R :: Pp :: Rp :: alpha :: nil) = 3) by (apply LPRPpRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPRPpRpalphaMtmp : rk(P :: R :: Pp :: Rp :: alpha :: nil) <= 3) by (solve_hyps_max HPRPpRpalphaeq HPRPpRpalphaM3).
	assert(HPRPpQpRpalphabetagammaeq : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) = 4) by (apply LPRPpQpRpalphabetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPRPpQpRpalphabetagammamtmp : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPRPpQpRpalphabetagammaeq HPRPpQpRpalphabetagammam4).
	assert(HPPpRpalphaeq : rk(P :: Pp :: Rp :: alpha :: nil) = 3) by (apply LPPpRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPPpRpalphamtmp : rk(P :: Pp :: Rp :: alpha :: nil) >= 3) by (solve_hyps_min HPPpRpalphaeq HPPpRpalpham3).
	assert(Hincl : incl (P :: Pp :: Rp :: alpha :: nil) (list_inter (P :: R :: Pp :: Rp :: alpha :: nil) (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) (P :: R :: Pp :: Rp :: alpha :: P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: Pp :: Rp :: alpha :: P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) ((P :: R :: Pp :: Rp :: alpha :: nil) ++ (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPRPpQpRpalphabetagammamtmp;try rewrite HT2 in HPRPpQpRpalphabetagammamtmp.
	assert(HT := rule_4 (P :: R :: Pp :: Rp :: alpha :: nil) (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) (P :: Pp :: Rp :: alpha :: nil) 4 3 3 HPRPpQpRpalphabetagammamtmp HPPpRpalphamtmp HPRPpRpalphaMtmp Hincl); apply HT.
}

assert(HPPpQpRpalphabetagammaM : rk(P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPPpQpRpalphabetagammam : rk(P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min HPPpQpRpalphabetagammaeq HPPpQpRpalphabetagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPPpQpalphabetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Pp :: Qp :: alpha :: beta :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PPpQpalphabetagamma requis par la preuve de (?)PPpQpalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PPpQpalphabetagamma requis par la preuve de (?)PPpQpalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PPpQpalphabetagamma requis par la preuve de (?)PPpQpalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPPpQpalphabetagammam2 : rk(P :: Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Pp :: Qp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Pp :: Qp :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPPpQpalphabetagammam3 : rk(P :: Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 3).
{
	assert(HPpQpalphaeq : rk(Pp :: Qp :: alpha :: nil) = 3) by (apply LPpQpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpQpalphamtmp : rk(Pp :: Qp :: alpha :: nil) >= 3) by (solve_hyps_min HPpQpalphaeq HPpQpalpham3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: alpha :: nil) (P :: Pp :: Qp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: alpha :: nil) (P :: Pp :: Qp :: alpha :: beta :: gamma :: nil) 3 3 HPpQpalphamtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma ::  de rang :  4 et 4 	 AiB : Pp :: Qp :: alpha ::  de rang :  3 et 3 	 A : Pp :: Qp :: Rp :: alpha ::   de rang : 3 et 3 *)
assert(HPPpQpalphabetagammam4 : rk(P :: Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 4).
{
	assert(HPpQpRpalphaeq : rk(Pp :: Qp :: Rp :: alpha :: nil) = 3) by (apply LPpQpRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpQpRpalphaMtmp : rk(Pp :: Qp :: Rp :: alpha :: nil) <= 3) by (solve_hyps_max HPpQpRpalphaeq HPpQpRpalphaM3).
	assert(HPPpQpRpalphabetagammaeq : rk(P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) = 4) by (apply LPPpQpRpalphabetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPPpQpRpalphabetagammamtmp : rk(P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPPpQpRpalphabetagammaeq HPPpQpRpalphabetagammam4).
	assert(HPpQpalphaeq : rk(Pp :: Qp :: alpha :: nil) = 3) by (apply LPpQpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpQpalphamtmp : rk(Pp :: Qp :: alpha :: nil) >= 3) by (solve_hyps_min HPpQpalphaeq HPpQpalpham3).
	assert(Hincl : incl (Pp :: Qp :: alpha :: nil) (list_inter (Pp :: Qp :: Rp :: alpha :: nil) (P :: Pp :: Qp :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) (Pp :: Qp :: Rp :: alpha :: P :: Pp :: Qp :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: Qp :: Rp :: alpha :: P :: Pp :: Qp :: alpha :: beta :: gamma :: nil) ((Pp :: Qp :: Rp :: alpha :: nil) ++ (P :: Pp :: Qp :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPPpQpRpalphabetagammamtmp;try rewrite HT2 in HPPpQpRpalphabetagammamtmp.
	assert(HT := rule_4 (Pp :: Qp :: Rp :: alpha :: nil) (P :: Pp :: Qp :: alpha :: beta :: gamma :: nil) (Pp :: Qp :: alpha :: nil) 4 3 3 HPPpQpRpalphabetagammamtmp HPpQpalphamtmp HPpQpRpalphaMtmp Hincl); apply HT.
}

assert(HPPpQpalphabetagammaM : rk(P :: Pp :: Qp :: alpha :: beta :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPPpQpalphabetagammam : rk(P :: Pp :: Qp :: alpha :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min HPPpQpalphabetagammaeq HPPpQpalphabetagammam1).
intuition.
Qed.

(* dans constructLemma(), requis par LPQPpQpalphabetagamma *)
(* dans la couche 0 *)
Lemma LPQPpQpRpalphabetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Q :: Pp :: Qp :: Rp :: alpha :: beta :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQPpQpRpalphabetagamma requis par la preuve de (?)PQPpQpRpalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQPpQpRp requis par la preuve de (?)PQPpQpRpalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour RPp requis par la preuve de (?)PQPpQpRp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQPpQpRp requis par la preuve de (?)PQPpQpRp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQPpQpRp requis par la preuve de (?)PQPpQpRp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQPpQpRpm2 : rk(P :: Q :: Pp :: Qp :: Rp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: Pp :: Qp :: Rp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: Pp :: Qp :: Rp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: -4 -2 et 5*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Rp ::  de rang :  4 et 4 	 AiB : Pp ::  de rang :  1 et 1 	 A : R :: Pp ::   de rang : 1 et 2 *)
assert(HPQPpQpRpm3 : rk(P :: Q :: Pp :: Qp :: Rp :: nil) >= 3).
{
	assert(HRPpMtmp : rk(R :: Pp :: nil) <= 2) by (solve_hyps_max HRPpeq HRPpM2).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(HPpmtmp : rk(Pp :: nil) >= 1) by (solve_hyps_min HPpeq HPpm1).
	assert(Hincl : incl (Pp :: nil) (list_inter (R :: Pp :: nil) (P :: Q :: Pp :: Qp :: Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (R :: Pp :: P :: Q :: Pp :: Qp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (R :: Pp :: P :: Q :: Pp :: Qp :: Rp :: nil) ((R :: Pp :: nil) ++ (P :: Q :: Pp :: Qp :: Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_4 (R :: Pp :: nil) (P :: Q :: Pp :: Qp :: Rp :: nil) (Pp :: nil) 4 1 2 HPQRPpQpRpmtmp HPpmtmp HRPpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQPpQpRpalphabetagamma requis par la preuve de (?)PQPpQpRpalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQPpQpRpalphabetagamma requis par la preuve de (?)PQPpQpRpalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQPpQpRpalphabetagammam2 : rk(P :: Q :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPQPpQpRpalphabetagammam3 : rk(P :: Q :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 3).
{
	assert(HPQPpQpRpmtmp : rk(P :: Q :: Pp :: Qp :: Rp :: nil) >= 3) by (solve_hyps_min HPQPpQpRpeq HPQPpQpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: Pp :: Qp :: Rp :: nil) (P :: Q :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: Pp :: Qp :: Rp :: nil) (P :: Q :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) 3 3 HPQPpQpRpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQPpQpRpalphabetagammam4 : rk(P :: Q :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 4).
{
	assert(HPQPpRpalphaeq : rk(P :: Q :: Pp :: Rp :: alpha :: nil) = 4) by (apply LPQPpRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQPpRpalphamtmp : rk(P :: Q :: Pp :: Rp :: alpha :: nil) >= 4) by (solve_hyps_min HPQPpRpalphaeq HPQPpRpalpham4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: Pp :: Rp :: alpha :: nil) (P :: Q :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: Pp :: Rp :: alpha :: nil) (P :: Q :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) 4 4 HPQPpRpalphamtmp Hcomp Hincl);apply HT.
}

assert(HPQPpQpRpalphabetagammaM : rk(P :: Q :: Pp :: Qp :: Rp :: alpha :: beta :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQPpQpRpalphabetagammam : rk(P :: Q :: Pp :: Qp :: Rp :: alpha :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min HPQPpQpRpalphabetagammaeq HPQPpQpRpalphabetagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPQPpQpalphabetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Q :: Pp :: Qp :: alpha :: beta :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQPpQpalphabetagamma requis par la preuve de (?)PQPpQpalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour PQRPpQpOoalphabetagamma requis par la preuve de (?)PQPpQpalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQpOoalphabetagamma requis par la preuve de (?)PQRPpQpOoalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQpOoalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpm2 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -1 et -2*)
assert(HPQRPpQpm3 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3).
{
	assert(HRpMtmp : rk(Rp :: nil) <= 1) by (solve_hyps_max HRpeq HRpM1).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) ((P :: Q :: R :: Pp :: Qp :: nil) ++ (Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_2 (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil) (nil) 4 0 1 HPQRPpQpRpmtmp Hmtmp HRpMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQpOoalphabetagamma requis par la preuve de (?)PQRPpQpOoalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQpOoalphabetagamma requis par la preuve de (?)PQRPpQpOoalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpOoalphabetagammam2 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPQRPpQpOoalphabetagammam3 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 3).
{
	assert(HPQRPpQpmtmp : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3) by (solve_hyps_min HPQRPpQpeq HPQRPpQpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) 3 3 HPQRPpQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpOoalphabetagammam4 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQPpQpalphabetagamma requis par la preuve de (?)PQPpQpalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQPpQpalphabetagamma requis par la preuve de (?)PQPpQpalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQPpQpalphabetagammam2 : rk(P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma ::  de rang :  4 et 4 	 AiB : P :: Pp ::  de rang :  2 et 2 	 A : P :: R :: Pp :: Oo ::   de rang : 3 et 3 *)
assert(HPQPpQpalphabetagammam3 : rk(P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 3).
{
	assert(HPRPpOoeq : rk(P :: R :: Pp :: Oo :: nil) = 3) by (apply LPRPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPRPpOoMtmp : rk(P :: R :: Pp :: Oo :: nil) <= 3) by (solve_hyps_max HPRPpOoeq HPRPpOoM3).
	assert(HPQRPpQpOoalphabetagammamtmp : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPQRPpQpOoalphabetagammaeq HPQRPpQpOoalphabetagammam4).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hincl : incl (P :: Pp :: nil) (list_inter (P :: R :: Pp :: Oo :: nil) (P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) (P :: R :: Pp :: Oo :: P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: Pp :: Oo :: P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil) ((P :: R :: Pp :: Oo :: nil) ++ (P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpOoalphabetagammamtmp;try rewrite HT2 in HPQRPpQpOoalphabetagammamtmp.
	assert(HT := rule_4 (P :: R :: Pp :: Oo :: nil) (P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil) (P :: Pp :: nil) 4 2 3 HPQRPpQpOoalphabetagammamtmp HPPpmtmp HPRPpOoMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : P :: Q :: Pp :: Qp :: Rp :: alpha :: beta :: gamma ::  de rang :  4 et 4 	 AiB : Pp :: Qp :: alpha ::  de rang :  3 et 3 	 A : Pp :: Qp :: Rp :: alpha ::   de rang : 3 et 3 *)
assert(HPQPpQpalphabetagammam4 : rk(P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 4).
{
	assert(HPpQpRpalphaeq : rk(Pp :: Qp :: Rp :: alpha :: nil) = 3) by (apply LPpQpRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpQpRpalphaMtmp : rk(Pp :: Qp :: Rp :: alpha :: nil) <= 3) by (solve_hyps_max HPpQpRpalphaeq HPpQpRpalphaM3).
	assert(HPQPpQpRpalphabetagammaeq : rk(P :: Q :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) = 4) by (apply LPQPpQpRpalphabetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQPpQpRpalphabetagammamtmp : rk(P :: Q :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPQPpQpRpalphabetagammaeq HPQPpQpRpalphabetagammam4).
	assert(HPpQpalphaeq : rk(Pp :: Qp :: alpha :: nil) = 3) by (apply LPpQpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpQpalphamtmp : rk(Pp :: Qp :: alpha :: nil) >= 3) by (solve_hyps_min HPpQpalphaeq HPpQpalpham3).
	assert(Hincl : incl (Pp :: Qp :: alpha :: nil) (list_inter (Pp :: Qp :: Rp :: alpha :: nil) (P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) (Pp :: Qp :: Rp :: alpha :: P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: Qp :: Rp :: alpha :: P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil) ((Pp :: Qp :: Rp :: alpha :: nil) ++ (P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQPpQpRpalphabetagammamtmp;try rewrite HT2 in HPQPpQpRpalphabetagammamtmp.
	assert(HT := rule_4 (Pp :: Qp :: Rp :: alpha :: nil) (P :: Q :: Pp :: Qp :: alpha :: beta :: gamma :: nil) (Pp :: Qp :: alpha :: nil) 4 3 3 HPQPpQpRpalphabetagammamtmp HPpQpalphamtmp HPpQpRpalphaMtmp Hincl); apply HT.
}

assert(HPQPpQpalphabetagammaM : rk(P :: Q :: Pp :: Qp :: alpha :: beta :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQPpQpalphabetagammam : rk(P :: Q :: Pp :: Qp :: alpha :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min HPQPpQpalphabetagammaeq HPQPpQpalphabetagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPQRPpOoalphabetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Oo :: alpha :: beta :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpOoalphabetagamma requis par la preuve de (?)PQRPpOoalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpOoalphabetagamma requis par la preuve de (?)PQRPpOoalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpOoalphabetagammam2 : rk(P :: Q :: R :: Pp :: Oo :: alpha :: beta :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Oo :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpOoalphabetagammam4 : rk(P :: Q :: R :: Pp :: Oo :: alpha :: beta :: gamma :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Oo :: alpha :: beta :: gamma :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

assert(HPQRPpOoalphabetagammaM : rk(P :: Q :: R :: Pp :: Oo :: alpha :: beta :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRPpOoalphabetagammam : rk(P :: Q :: R :: Pp :: Oo :: alpha :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min HPQRPpOoalphabetagammaeq HPQRPpOoalphabetagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPQRPpQpOoalphabetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQpOoalphabetagamma requis par la preuve de (?)PQRPpQpOoalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQpOoalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQp requis par la preuve de (?)PQRPpQp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpm2 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -1 et -2*)
assert(HPQRPpQpm3 : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3).
{
	assert(HRpMtmp : rk(Rp :: nil) <= 1) by (solve_hyps_max HRpeq HRpM1).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: nil) ((P :: Q :: R :: Pp :: Qp :: nil) ++ (Rp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpmtmp;try rewrite HT2 in HPQRPpQpRpmtmp.
	assert(HT := rule_2 (P :: Q :: R :: Pp :: Qp :: nil) (Rp :: nil) (nil) 4 0 1 HPQRPpQpRpmtmp Hmtmp HRpMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRPpQpOoalphabetagamma requis par la preuve de (?)PQRPpQpOoalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQpOoalphabetagamma requis par la preuve de (?)PQRPpQpOoalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpOoalphabetagammam2 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HPQRPpQpOoalphabetagammam3 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 3).
{
	assert(HPQRPpQpmtmp : rk(P :: Q :: R :: Pp :: Qp :: nil) >= 3) by (solve_hyps_min HPQRPpQpeq HPQRPpQpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Pp :: Qp :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) 3 3 HPQRPpQpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPQRPpQpOoalphabetagammam4 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 4).
{
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}

assert(HPQRPpQpOoalphabetagammaM : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRPpQpOoalphabetagammam : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min HPQRPpQpOoalphabetagammaeq HPQRPpQpOoalphabetagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma Lalphabetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->
rk(alpha :: beta :: gamma ::  nil) = 2.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour alphabetagamma requis par la preuve de (?)alphabetagamma pour la règle 3  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PpQpalphabetagamma requis par la preuve de (?)alphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PpQpalphabetagamma requis par la preuve de (?)PpQpalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRPpQpalphabetagamma requis par la preuve de (?)PpQpalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpQpalphabetagamma requis par la preuve de (?)PRPpQpalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpQpalphabetagamma requis par la preuve de (?)PRPpQpalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPRPpQpalphabetagammam2 : rk(P :: R :: Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 2).
{
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Qp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Qp :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 4 -4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma ::  de rang :  4 et 4 	 AiB : P :: Pp ::  de rang :  2 et 2 	 A : P :: Q :: Pp :: Oo ::   de rang : 3 et 3 *)
assert(HPRPpQpalphabetagammam3 : rk(P :: R :: Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 3).
{
	assert(HPQPpOoeq : rk(P :: Q :: Pp :: Oo :: nil) = 3) by (apply LPQPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQPpOoMtmp : rk(P :: Q :: Pp :: Oo :: nil) <= 3) by (solve_hyps_max HPQPpOoeq HPQPpOoM3).
	assert(HPQRPpQpOoalphabetagammaeq : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) = 4) by (apply LPQRPpQpOoalphabetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPQRPpQpOoalphabetagammamtmp : rk(P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPQRPpQpOoalphabetagammaeq HPQRPpQpOoalphabetagammam4).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hincl : incl (P :: Pp :: nil) (list_inter (P :: Q :: Pp :: Oo :: nil) (P :: R :: Pp :: Qp :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) (P :: Q :: Pp :: Oo :: P :: R :: Pp :: Qp :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: Pp :: Oo :: P :: R :: Pp :: Qp :: alpha :: beta :: gamma :: nil) ((P :: Q :: Pp :: Oo :: nil) ++ (P :: R :: Pp :: Qp :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpOoalphabetagammamtmp;try rewrite HT2 in HPQRPpQpOoalphabetagammamtmp.
	assert(HT := rule_4 (P :: Q :: Pp :: Oo :: nil) (P :: R :: Pp :: Qp :: alpha :: beta :: gamma :: nil) (P :: Pp :: nil) 4 2 3 HPQRPpQpOoalphabetagammamtmp HPPpmtmp HPQPpOoMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PpQpalphabetagamma requis par la preuve de (?)PpQpalphabetagamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : P :: R :: Pp :: Qp :: alpha :: beta :: gamma ::  de rang :  3 et 4 	 AiB : alpha ::  de rang :  1 et 1 	 A : P :: R :: alpha ::   de rang : 2 et 2 *)
assert(HPpQpalphabetagammam2 : rk(Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 2).
{
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	assert(HPRPpQpalphabetagammamtmp : rk(P :: R :: Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 3) by (solve_hyps_min HPRPpQpalphabetagammaeq HPRPpQpalphabetagammam3).
	assert(Halphamtmp : rk(alpha :: nil) >= 1) by (solve_hyps_min Halphaeq Halpham1).
	assert(Hincl : incl (alpha :: nil) (list_inter (P :: R :: alpha :: nil) (Pp :: Qp :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: Qp :: alpha :: beta :: gamma :: nil) (P :: R :: alpha :: Pp :: Qp :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: alpha :: Pp :: Qp :: alpha :: beta :: gamma :: nil) ((P :: R :: alpha :: nil) ++ (Pp :: Qp :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPRPpQpalphabetagammamtmp;try rewrite HT2 in HPRPpQpalphabetagammamtmp.
	assert(HT := rule_4 (P :: R :: alpha :: nil) (Pp :: Qp :: alpha :: beta :: gamma :: nil) (alpha :: nil) 3 1 2 HPRPpQpalphabetagammamtmp Halphamtmp HPRalphaMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPpQpalphabetagammam3 : rk(Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 3).
{
	assert(HPpQpalphaeq : rk(Pp :: Qp :: alpha :: nil) = 3) by (apply LPpQpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpQpalphamtmp : rk(Pp :: Qp :: alpha :: nil) >= 3) by (solve_hyps_min HPpQpalphaeq HPpQpalpham3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: alpha :: nil) (Pp :: Qp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: alpha :: nil) (Pp :: Qp :: alpha :: beta :: gamma :: nil) 3 3 HPpQpalphamtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour alphabetagamma requis par la preuve de (?)alphabetagamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : Pp :: Qp :: alpha :: beta :: gamma ::  de rang :  3 et 4 	 AiB : beta ::  de rang :  1 et 1 	 A : Pp :: Qp :: beta ::   de rang : 2 et 2 *)
assert(Halphabetagammam2 : rk(alpha :: beta :: gamma :: nil) >= 2).
{
	assert(HPpQpbetaMtmp : rk(Pp :: Qp :: beta :: nil) <= 2) by (solve_hyps_max HPpQpbetaeq HPpQpbetaM2).
	assert(HPpQpalphabetagammamtmp : rk(Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 3) by (solve_hyps_min HPpQpalphabetagammaeq HPpQpalphabetagammam3).
	assert(Hbetamtmp : rk(beta :: nil) >= 1) by (solve_hyps_min Hbetaeq Hbetam1).
	assert(Hincl : incl (beta :: nil) (list_inter (Pp :: Qp :: beta :: nil) (alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Pp :: Qp :: alpha :: beta :: gamma :: nil) (Pp :: Qp :: beta :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: Qp :: beta :: alpha :: beta :: gamma :: nil) ((Pp :: Qp :: beta :: nil) ++ (alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPpQpalphabetagammamtmp;try rewrite HT2 in HPpQpalphabetagammamtmp.
	assert(HT := rule_4 (Pp :: Qp :: beta :: nil) (alpha :: beta :: gamma :: nil) (beta :: nil) 3 1 2 HPpQpalphabetagammamtmp Hbetamtmp HPpQpbetaMtmp Hincl); apply HT.
}

(* Application de la règle 3 code (6 dans la thèse) *)
(* marque des antécédents A B AUB: 4 4 et 4*)
assert(HalphabetagammaM2 : rk(alpha :: beta :: gamma :: nil) <= 2).
{
	assert(HPalphabetagammaeq : rk(P :: alpha :: beta :: gamma :: nil) = 3) by (apply LPalphabetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPalphabetagammaMtmp : rk(P :: alpha :: beta :: gamma :: nil) <= 3) by (solve_hyps_max HPalphabetagammaeq HPalphabetagammaM3).
	assert(HPpQpalphabetagammaeq : rk(Pp :: Qp :: alpha :: beta :: gamma :: nil) = 3) by (apply LPpQpalphabetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPpQpalphabetagammaMtmp : rk(Pp :: Qp :: alpha :: beta :: gamma :: nil) <= 3) by (solve_hyps_max HPpQpalphabetagammaeq HPpQpalphabetagammaM3).
	assert(HPPpQpalphabetagammaeq : rk(P :: Pp :: Qp :: alpha :: beta :: gamma :: nil) = 4) by (apply LPPpQpalphabetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption).
	assert(HPPpQpalphabetagammamtmp : rk(P :: Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPPpQpalphabetagammaeq HPPpQpalphabetagammam4).
	assert(Hincl : incl (alpha :: beta :: gamma :: nil) (list_inter (P :: alpha :: beta :: gamma :: nil) (Pp :: Qp :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Pp :: Qp :: alpha :: beta :: gamma :: nil) (P :: alpha :: beta :: gamma :: Pp :: Qp :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: alpha :: beta :: gamma :: Pp :: Qp :: alpha :: beta :: gamma :: nil) ((P :: alpha :: beta :: gamma :: nil) ++ (Pp :: Qp :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPPpQpalphabetagammamtmp;try rewrite HT2 in HPPpQpalphabetagammamtmp.
	assert(HT := rule_3 (P :: alpha :: beta :: gamma :: nil) (Pp :: Qp :: alpha :: beta :: gamma :: nil) (alpha :: beta :: gamma :: nil) 3 3 4 HPalphabetagammaMtmp HPpQpalphabetagammaMtmp HPPpQpalphabetagammamtmp Hincl);apply HT.
}
try clear HPpQpalphabetagammaM1. try clear HPpQpalphabetagammaM2. try clear HPpQpalphabetagammaM3. try clear HPpQpalphabetagammam4. try clear HPpQpalphabetagammam3. try clear HPpQpalphabetagammam2. try clear HPpQpalphabetagammam1. 

assert(HalphabetagammaM : rk(alpha :: beta :: gamma ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max Halphabetagammaeq HalphabetagammaM3).
assert(Halphabetagammam : rk(alpha :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min Halphabetagammaeq Halphabetagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Theorem def_Conclusion : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2 ->
rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 -> rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 ->
rk(Q :: Qp :: Oo ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 ->
rk(P :: R :: alpha ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 ->
rk(Pp :: Qp :: beta ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 ->

	 rk(alpha :: beta :: gamma ::  nil) = 2  .
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPPpeq HQQpeq HRRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq HPpQpRpOoeq HPRalphaeq
HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .
repeat split.

	apply Lalphabetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ; assumption.
Qed .
