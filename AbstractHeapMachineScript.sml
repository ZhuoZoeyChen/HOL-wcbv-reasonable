open HolKernel Parse boolLib bossLib;
open arithmeticTheory;
open listTheory;
open PrelimsTheory;
open LTheory;
open ProgramsTheory;

val _ = new_theory "AbstractHeapMachine";

(* ------------------
        Heaps
   ------------------ *)

Type HA = ``:num``;

Datatype:
  clos = closC Pro HA
End

(*
  Inductive clos :=
    closC (P:Pro) (a:HA).
  Notation "P ! a" := (closC P a) (at level 40).
*)

Datatype:
  heapEntry = heapEntryC clos HA
End

Type Heap = ``:heapEntry list``;

Definition put:
  put H e = (H++[e], LENGTH H)
End

Definition get:
  get H alpha = nth_error alpha H
End

Definition extended:
  extended H H' =
    (∀alpha m. (get H alpha = SOME m) ⇒ (get H' alpha = SOME m))
End

(*
  Inductive heapEntry := heapEntryC (g:clos) (alpha:HA).

Heaps
  Let Heap := list heapEntry.
  Implicit Type H : Heap.
  Definition put H e := (H++[e],|H|).
  Definition get H alpha:= nth_error H alpha.
  Definition extended H H' :=
    forall alpha m, get H alpha = Some m -> get H' alpha = Some m.
*)

Theorem get_current:
  ∀H m H' alpha.
    put H m = (H', alpha) ⇒ get H' alpha = SOME m
Proof
  rw[put, get] >>
  `LENGTH H ≤ LENGTH H` by simp[] >>
  drule nth_error_app2 >> rw[] >>
  rw[Once nth_error]
QED

Theorem put_extends:
  ∀H H' m b.
    put H m = (H', b) ⇒ extended H H'
Proof
  rw[put, extended, get] >>
  metis_tac[nth_error_Some_lt, nth_error_app1]
QED

Definition lookup:
  lookup (H: Heap) (alpha:num) (x:num) =
    case (get H alpha) of
      SOME (heapEntryC bd env')
        => (case x of
              0 => SOME bd
            | SUC x' => lookup H env' x')
    | _ => NONE
End

(* ------------------
    Reduction Rules
   ------------------ *)


            (* Task stack # Value stack # Heap *)
Type state = ``:clos list # clos list # Heap``;

(* heap machine reduction rules

state -> state

lam: extracts the function body, put it on the value stack

app: (?) if H' = H++[(heapEntryC g b)], and,  c = LENGTH H
      pull value out from value stack and push it to task stack

var: substitution value from heap, put it on the value stack

nil: skip to next

*)

Inductive step:
[~pushVal:]
  (∀P P' Q a T V H.
    jumpTarget 0 [] P = SOME (Q, P')
    ⇒ step (closC (lamT::P) a::T, V, H) (closC P' a::T, closC Q a::V, H)) ∧
[~beta:]
  (∀a b g P Q H H' c T V.
    put H (heapEntryC g b) = (H', c)
    ⇒ step (closC (appT::P) a::T, g::closC Q b::V, H) (closC Q c::closC P a::T, V, H')) ∧
[~load:]
  (∀P a x g T V H.
    lookup H a x = SOME g
    ⇒ step (closC (varT x::P) a::T, V, H) (closC P a::T, g::V, H)) ∧
[~nil:]
  (∀a T V H.
    step (closC [] a::T, V, H) (T, V, H))
End

(*
  Inductive step : state -> state -> Prop :=
    step_pushVal P P' Q a T V H:
      jumpTarget 0 [] P = Some (Q,P')
      ->step ((lamT::P)!a::T,V,H) (P'!a::T,Q!a::V,H)
  | step_beta a b g P Q H H' c T V:
      put H (heapEntryC g b) = (H',c)
      -> step ((appT::P)!a::T,g::Q!b::V,H) (Q!c ::P!a::T,V,H')
  | step_load P a x g T V H:
      lookup H a x = Some g
      -> step ((varT x::P)!a::T,V,H) (P!a::T,g::V,H)
  | step_nil a T V H: step ([]!a::T,V,H) (T,V,H).

  Hint Constructors step.
*)

(* ------------------
        Unfolding
   ------------------ *)

Inductive unfolds:
[~Unbound:]
  (∀H k n.
    n < k ⇒ unfolds H a k (var n) (var n)) ∧
[~Bound:]
  (∀H k b P s s' n.
    k ≤ n ∧
    lookup H a (n-k) = SOME (closC P b) ∧
    reprP P s ∧
    unfolds H b 0 s s' ⇒
    unfolds H a k (var n) s') ∧
[~Lam:]
  (∀H k s s'.
    unfolds H a (SUC k) s s' ⇒
    unfolds H a k (lam s) (lam s')) ∧
[~App:]
  (∀H k s t s' t'.
    unfolds H a k s s' ∧
    unfolds H a k t t' ⇒
    unfolds H a k (app s t) (app s' t'))
End

Theorem unfolds_bound:
  ∀H k s s' a.
    unfolds H a k s s' ⇒ bound k s'
Proof
  Induct_on `unfolds` >> rw[] (* 4 *)
  >- rw[Once bound_cases]
  >- (fs[Once reprP_cases] >> rw[] >>
      qpat_x_assum `unfolds _ _ _ _ _` mp_tac >>
      rw[Once unfolds_cases] >>
      rw[Once bound_cases] >>
      qpat_x_assum `bound _ _` mp_tac >>
      rw[Once bound_cases] >>
      irule bound_ge >> qexists_tac `1` >>
      rw[])
  >> rw[Once bound_cases]
QED

Inductive reprC:
[~C:]
  (∀H P s a s'.
    reprP P s ∧
    unfolds H a 0 s s' ⇒
    reprC H (closC P a) s')
End

(*
  Inductive reprC : Heap -> clos -> term -> Prop :=
    reprCC H P s a s' :
      reprP P s ->
      unfolds H a 0 s s' ->
      reprC H (P!a) s'.
*)

Theorem unfolds_subst':
  ∀H s s' t' a a' k g.
    get H a' = SOME (heapEntryC g a) ⇒
    reprC H g t' ⇒
    unfolds H a (SUC k) s s' ⇒
    unfolds H a' k s (subst s' k t')
Proof
  Induct_on `unfolds` >> rw[]
    >- (rw[Once unfolds_cases] >> Cases_on `n < k` >> rw[]
       >- rw[Once subst]
        >> fs[NOT_LESS] >> rw[Once lookup] >>
        `n ≤ k` by fs[LESS_EQ_IFF_LESS_SUC] >>
        `n = k` by rw[] >> rw[] >>
        fs[get] >> Cases_on `g` >> rw[] >>
        fs[Once reprC_cases] >>
       qexists_tac `s`  >> rw[] >>
       rw[Once subst])
    >- (rename [`lookup H a (n − SUC k) = SOME (closC P b)`,
                `get H a' = SOME (heapEntryC g a)`] >>
        `lookup H a' (n − k) = SOME (closC P b)`
            by (Cases_on `n` >> rw[] >> fs[] >>
                `lookup H a' (SUC (n' − k)) = SOME (closC P b)`
                    suffices_by (rw[] >> fs[SUB_LEFT_SUC] >>
                                 Cases_on `n' ≤ k` >> gs[] >>
                                 `k = n'` by gs[integerTheory.INT_LE_ANTISYM] >>
                                 rw[]) >>
                rw[Once lookup]) >>
        `bound k s'`
            by (drule unfolds_bound >> rw[] >>
                `0 ≤ k` by simp[] >> metis_tac[bound_ge]) >>
        rw[bound_closed_k] >> rw[Once unfolds_cases] >> metis_tac[])
    >- (rw[Once unfolds_cases] >> rw[Once subst])
    >> rw[Once unfolds_cases] >> rw[Once subst]
QED

Theorem unfolds_subst:
  ∀H s s' t' a a' g.
    get H a' = SOME (heapEntryC g a) ⇒
    reprC H g t' ⇒
    unfolds H a 1 s s' ⇒
    unfolds H a' 0 s (subst s' 0 t')
Proof
  metis_tac[unfolds_subst', ONE]
QED

Theorem bound_unfolds_id:
  ∀H k s a.
    bound k s ⇒ unfolds H a k s s
Proof
  Induct_on `s` >> rw[]
  >- fs[Once unfolds_cases, Once bound_cases]
  >- (qpat_x_assum `bound _ _` mp_tac >>
      rw[Once unfolds_cases, Once bound_cases])
  >> qpat_x_assum `bound _ _` mp_tac >>
  rw[Once unfolds_cases, Once bound_cases]
QED

(*-------
A PreOrder is both Reflexive and Transitive.

  Class PreOrder (R : relation A) : Prop := {
    PreOrder_Reflexive :> Reflexive R | 2 ;
    PreOrder_Transitive :> Transitive R | 2 }.
 --------*)

(*
  Instance extended_PO :
    PreOrder extended.
  Proof.
    unfold extended;split;repeat intro. all:eauto.
  Qed.
  Typeclasses Opaque extended.
*)

Theorem lookup_extend:
  ∀H H' a x g.
    extended H H' ⇒
    lookup H a x = SOME g ⇒
    lookup H' a x = SOME g
Proof
  Induct_on `x` >> rw[]
  >- (fs[extended] >> fs[lookup] >>
      Cases_on `get H a` >> fs[] >>
      first_x_assum drule >> rw[])
  >> qpat_x_assum `lookup _ _ _ = _` mp_tac >>
  rw[Once lookup] >> rw[Once lookup] >>
  Cases_on `get H a` >> fs[] >>
  rename [`extended H H'`] >>
  `∀alpha m. get H alpha = SOME m ⇒ get H' alpha = SOME m`
    by (qpat_x_assum `extended _ _` mp_tac >> rw[extended]) >>
  first_x_assum drule >> rw[] >>
  Cases_on `x'` >> fs[] >>
  metis_tac[]
QED

Theorem unfolds_extend:
  ∀H H' a s t k.
    extended H H' ⇒
    unfolds H a k s t ⇒
    unfolds H' a k s t
Proof
  Induct_on `unfolds` >> rw[]
  >- (fs[extended] >> rw[Once unfolds_cases])
  >> rw[Once unfolds_cases] >>
  drule_all lookup_extend >> rw[] >>
  metis_tac[]
QED

Theorem reprC_extend:
  ∀H H' g s.
    extended H H' ⇒
    reprC H g s ⇒
    reprC H' g s
Proof
  Induct_on `reprC` >> rw[reprC_cases] >>
  metis_tac[unfolds_extend]
QED

(* ------------------
          Time
   ------------------ *)

Theorem correctTime':
  ∀s t k s0 P a T V H.
    timeBS k s t ⇒
    unfolds H a 0 s0 s ⇒
    ∃g l H'.
      reprC H' g t ∧
      pow step l ((closC (compile s0++P) a)::T,V,H)
        ((closC P a)::T,g::V,H') ∧
      l = 4*k+1 ∧
      extended H H'
Proof
  Induct_on `timeBS` >> rw[]
  >- (fs[Once unfolds_cases] >> rw[]
      >- (qexistsl_tac [`closC P' b`, `H`] >> rw[]
          >- (rw[reprC_cases] >> metis_tac[])
          >- (rw[Once compile] >>
              `step (closC (varT n::P) a::T',V,H)
                    (closC P a::T',closC P' b::V,H)`
                  suffices_by metis_tac[rcomp_1] >>
              rw[Once step_cases])
          >> rw[extended])
      >> qexistsl_tac [`closC (compile s') a`, `H`] >> rw[]
      >- (rw[Once reprC_cases, Once reprP_cases] >>
          rw[Once unfolds_cases] >> metis_tac[])
      >- (rw[Once compile] >>
          `step (closC (lamT::(compile s' ⧺ [retT] ⧺ P)) a::T',V,H)
                (closC P a::T',closC (compile s') a::V,H)`
              suffices_by metis_tac[rcomp_1] >>
          rw[Once step_cases] >>
          `compile s' ⧺ [retT] ⧺ P = compile s' ++ retT :: P`
            suffices_by metis_tac[jumpTarget_correct] >>
          rw[rich_listTheory.CONS_APPEND])
      >> rw[extended])
  >> rename [`timeBS k' t (lam t')`, `timeBS k'' (subst s' 0 (lam t')) u`] >>
  pop_assum mp_tac >> rw[Once unfolds_cases]
  >- (fs[reprP_cases] >> rw[] >> fs[Once unfolds_cases])
  >> rename [`unfolds H a 0 t1 t`] >> rw[Once compile] >>
  last_x_assum (qspecl_then [`s''`, `compile t1 ++ appT::P`, `a`, `T'`, `V`, `H`] ASSUME_TAC) >>
  first_x_assum drule >> rw[] >>
  qpat_x_assum `reprC H' g (lam s')` mp_tac >>
  rw[reprC_cases, reprP_cases] >> rw[] >>
  qpat_x_assum `unfolds H' a' 0 (lam s'⁴') (lam s')` mp_tac >>
  rw[Once unfolds_cases] >>
  drule_all unfolds_extend >> rw[] >>
  rename [`unfolds Heap1 a2 1 s2 s'`] >>
  last_x_assum (qspecl_then [`t1`, `appT::P`, `a`, `T'`, `closC (compile s2) a2::V`, `Heap1`] ASSUME_TAC) >>
  first_x_assum drule >> rw[] >>
  rename [`extended Heap1 Heap2`] >>
  `∃Heap2' a2'. put Heap2 (heapEntryC g a2) = (Heap2', a2')`
    by rw[put] >>
  `extended Heap2 Heap2'`
    by metis_tac[put_extends] >>
  drule_all reprC_extend >> rw[] >>
  `unfolds Heap2' a2 1 s2 s'`
    by metis_tac[unfolds_extend] >>
  `unfolds Heap2' a2' 0 s2 (subst s' 0 (lam t'))`
    by metis_tac[unfolds_subst, get_current] >>
  last_x_assum (qspecl_then [`s2`, `[]`, `a2'`, `closC P a::T'`, `V`, `Heap2'`] ASSUME_TAC) >>
  first_x_assum drule >> rw[] >>
  rename [`reprC Heap3 g' u`] >>
  qexistsl_tac [`g'`, `Heap3`] >> rw[]
  >- (fs[reprC_cases, reprP_cases] >> metis_tac[])
  >- (`4 * k + 1 + ((4 * k' + 1) + ((4 * k'' + 1) + 1 + 1)) =
       4 * (k + (k' + (k'' + 1))) + 1`
        by rw[] >>
      `pow step (4 * k + 1 + ((4 * k' + 1) + ((4 * k'' + 1) + 1 + 1)))
          (closC (compile s'' ⧺ compile t1 ⧺ [appT] ⧺ P) a::T',V,H)
          (closC P a::T',g'::V,Heap3)`
        suffices_by rw[] >>
      pop_assum (K all_tac) >>
      irule (iffRL pow_add) >> rw[Once rcomp] >>
      qexists_tac `(closC (compile t1 ⧺ appT::P) a::T',closC (compile s2) a2::V,Heap1)` >>
      rw[]
      >- (`compile s'' ⧺ compile t1 ⧺ appT::P = compile s'' ⧺ compile t1 ⧺ [appT] ⧺ P`
          suffices_by metis_tac[] >>
        rw[rich_listTheory.CONS_APPEND])
      >> `pow step ((4 * k' + 1) + ((4 * k'' + 1) + 1 + 1))
          (closC (compile t1 ⧺ appT::P) a::T',closC (compile s2) a2::V,Heap1)
          (closC P a::T',g'::V,Heap3)`
          suffices_by rw[] >>
      irule (iffRL pow_add) >> rw[Once rcomp] >>
      qexists_tac `(closC (appT::P) a::T',g::closC (compile s2) a2::V,Heap2)` >>
      rw[] >>
      `pow step (1 + ((4 * k'' + 1) + 1))
          (closC (appT::P) a::T',g::closC (compile s2) a2::V,Heap2)
          (closC P a::T',g'::V,Heap3)`
        suffices_by rw[] >>
      irule (iffRL pow_add) >> rw[Once rcomp] >>
      `step (closC (appT::P) a::T',g::closC (compile s2) a2::V,Heap2)
          (closC (compile s2) a2'::closC P a::T',V,Heap2')`
        by metis_tac[step_cases] >>
      qexists_tac `closC (compile s2) a2'::closC P a::T',V,Heap2'` >>
      rw[rcomp_1] >>
      `pow step ((4 * k'' + 1) + 1)
        (closC (compile s2) a2'::closC P a::T',V,Heap2')
        (closC P a::T',g'::V,Heap3)`
        suffices_by rw[] >>
      irule (iffRL pow_add) >> rw[Once rcomp] >>
      qexists_tac `(closC [] a2'::closC P a::T',g'::V,Heap3)` >>
      rw[] >>
      metis_tac[step_cases, rcomp_1])
  >> metis_tac[extended]
QED

(*
  Definition init s :state := ([compile s!0],[],[]).
*)
Definition init_def:
  init s =
    ([closC (compile s) 0], [], [])
End

Theorem correctTime:
∀k s t.
  timeBS k s t ⇒
  closed s ⇒
  ∃g H.
    reprC H g t
    ∧ pow step (4*k+2) (init s)
               ([],[g],H)
Proof
  rw[] >>
  `∀s t k s0 P a T V H.
    timeBS k s t ⇒
    unfolds H a 0 s0 s ⇒
    ∃g l H'.
      reprC H' g t ∧
      pow step l ((closC (compile s0++P) a)::T,V,H)
        ((closC P a)::T,g::V,H') ∧
      l = 4*k+1 ∧
      extended H H'`
    by metis_tac[correctTime'] >>
  first_x_assum (qspecl_then [`s`, `t`, `k`, `s`, `[]`, `0`, `[]`, `[]`, `[]`] ASSUME_TAC) >>
  first_x_assum drule >> rw[] >>
  `bound 0 s ⇒ unfolds [] 0 0 s s` by metis_tac[bound_unfolds_id] >>
  fs[closed] >> first_x_assum drule >> rw[] >>
  first_x_assum drule >> rw[] >>
  qexistsl_tac [`g`, `H'`] >> rw[] >>
  rw[init_def] >>
  `pow step (4 * k + 1 + 1) ([closC (compile s) 0],[],[]) ([],[g],H')`
    suffices_by rw[] >>
  irule (iffRL pow_add) >> rw[Once rcomp] >>
  qexists_tac `([closC [] 0],[g],H')` >> rw[] >>
  metis_tac[step_cases, rcomp_1]
QED

(*

Notation "a ! alpha" := (closC a alpha) (at level 40).

*)

Theorem lookup_el:
  ∀H alpha x e.
    lookup H alpha x = SOME e ⇒
    ∃beta.
      MEM (heapEntryC e beta) H
Proof
  Induct_on `x` >> rw[]
  >- (fs[Once lookup, Once get] >>
      Cases_on `nth_error alpha H` >> fs[] >>
      drule nth_error_In >> rw[] >>
      Cases_on `x` >> fs[] >> rw[] >>
      metis_tac[])
  >> qpat_x_assum `lookup _ _ _ = _` mp_tac >>
  rw[Once lookup] >>
  Cases_on `get H alpha` >> gs[] >>
  Cases_on `x'` >> gs[] >>
  first_x_assum drule >> rw[]
QED
(*

Section Analysis.

  Variable s : term.*)
 (* Hypothesis cs : closed s.*)
 (*
  Variable T V : list clos.
  Variable H: list heapEntry.
  Variable i : nat.

  Hypothesis R: pow step i (init s) (T,V,H).
*)

(*
i s T V H
pow step i (init s) (T,V,H) ∧
*)

Theorem jumpTarget_eq':
  ∀k c c0 c1 c2.
    jumpTarget k c0 c = SOME (c1,c2)
    ⇒ c1++[retT]++c2=c0++c
Proof
  Induct_on `c` >> rw[]
  >- fs[Once jumpTarget]
  >> pop_assum mp_tac >>
  rw[Once jumpTarget] >> Cases_on `h` >> gs[]
  >- (first_x_assum drule >> rw[])
  >- (first_x_assum drule >> rw[])
  >- (first_x_assum drule >> rw[])
  >> Cases_on `k` >> gs[] >>
  metis_tac[]
QED

Theorem jumpTarget_eq:
  ∀c c0 c1 c2.
    jumpTarget 0 c0 c = SOME (c1,c2)
    ⇒ c1++[retT]++c2=c0++c
Proof
  metis_tac[jumpTarget_eq']
QED

(* ------------------
        Space
   ------------------ *)

(*
If we can reach (T, V, H) by taking i steps from initial state (init s),
then we have
  1. If (closC P a) is in (T++V),
     then
        1). size of the program-token list P <= 2* size of the lambda term s
        and
        2). a <= length of H
  2. For all members of H with heapEntryC (closC P a) beta, for any beta,
     we have that
        1). size of the program-token list P <= 2*size of the lambda term s
        and
        2). a <= length of H
        and
        3). beta <= length of H
*)

Theorem size_clos:
  ∀P a i s T V H.
    pow step i (init s) (T,V,H) ⇒
    (MEM (closC P a) (T++V) ⇒ sizeP P ≤ 2*size s ∧ a ≤ LENGTH H)
    ∧
    (∀beta.
      MEM (heapEntryC (closC P a) beta) H ⇒
      sizeP P ≤ 2*size s ∧ a ≤ LENGTH H ∧ beta ≤ LENGTH H)
Proof
  simp[sizeP] >>
  Induct_on `i` >> rw[]
  (* base cases *)
  (* 7 *)
  >- (fs[pow, it_def, rcomp, Once step_cases, eq_cases, init_def] >>
      gs[] >> rw[] >> metis_tac[sizeP_size])
  >- (fs[pow, it_def, rcomp, Once step_cases, eq_cases, init_def] >>
      gs[])
  >- (fs[pow, it_def, rcomp, Once step_cases, eq_cases, init_def] >>
      gs[])
  >- (fs[pow, it_def, rcomp, Once step_cases, eq_cases, init_def] >>
      gs[])
  >- (fs[pow, it_def, rcomp, Once step_cases, eq_cases, init_def] >>
      gs[])
  >- (fs[pow, it_def, rcomp, Once step_cases, eq_cases, init_def] >>
      gs[])
  >- (fs[pow, it_def, rcomp, Once step_cases, eq_cases, init_def] >>
      gs[])
  (* Inductive cases *)
  (* 7 *)
  (* MEM (closC P a) T' *)
    (* ==> SUM (MAP sizeT P) + 1 ≤ 2 * size s *)
  >- (fs[ADD1] >> drule (iffLR pow_add) >> rw[] >>
      pop_assum mp_tac >> rw[Once rcomp] >>
      rename [`pow step 1 y (T',V,H)`] >>
      `step y (T', V, H)` by metis_tac[rcomp_1] >>
      PairCases_on `y` >> gs[] >>
      first_x_assum drule >> rw[] >>
      qpat_x_assum `step _ _` mp_tac >> rw[Once step_cases]
      >- (drule jumpTarget_eq >> rw[] >> gs[] >>
          fs[MEM] >> rw[]
          >- (`SUM (MAP sizeT (lamT::(Q ⧺ [retT] ⧺ P))) + 1 ≤ 2 * size s`
                by metis_tac[] >>
              fs[SUM, MAP, sizeT] >>
              `SUM (MAP sizeT P) + 1
                ≤ SUM (MAP sizeT Q ⧺ [1] ⧺ MAP sizeT P) + 2`
                by rw[SUM_APPEND] >>
              rw[integerTheory.INT_LE_TRANS])
          >> metis_tac[])
      >- (fs[put] >> rw[]
          >- (`SUM (MAP sizeT (appT::P)) + 1 ≤ 2 * size s`
                by metis_tac[] >>
              fs[SUM, MAP, sizeT, SUM_APPEND, integerTheory.INT_LE_TRANS])
          >> metis_tac[])
      >- (fs[] >> rw[]
          >- (`SUM (MAP sizeT (varT x::P)) + 1 ≤ 2 * size s`
                by metis_tac[] >>
              fs[SUM, MAP, sizeT, SUM_APPEND, integerTheory.INT_LE_TRANS])
          >> metis_tac[])
      >> fs[] >> metis_tac[])
    (* a ≤ LENGTH H *)
  >- (fs[ADD1] >> drule (iffLR pow_add) >> rw[] >>
      pop_assum mp_tac >> rw[Once rcomp] >>
      rename [`pow step 1 y (T',V,H)`] >>
      `step y (T', V, H)` by metis_tac[rcomp_1] >>
      PairCases_on `y` >> gs[] >>
      first_x_assum drule >> rw[] >>
      qpat_x_assum `step _ _` mp_tac >> rw[Once step_cases]
      >- (drule jumpTarget_eq >> rw[] >> gs[] >>
          fs[MEM] >> rw[] >>
          metis_tac[])
      >- (fs[put] >> rw[] >> fs[] >> rw[]
          >- (`a ≤ LENGTH y2` by metis_tac[] >> rw[])
          >> `a ≤ LENGTH y2` by metis_tac[] >> rw[])
      >- (fs[] >> rw[] >> metis_tac[])
      >> fs[] >> rw[] >> metis_tac[])
  (* MEM (closC P a) V *)
    (* SUM (MAP sizeT P) + 1 ≤ 2 * size s *)
  >- (fs[ADD1] >> drule (iffLR pow_add) >> rw[] >>
      pop_assum mp_tac >> rw[Once rcomp] >>
      rename [`pow step 1 y (T',V,H)`] >>
      `step y (T', V, H)` by metis_tac[rcomp_1] >>
      PairCases_on `y` >> gs[] >>
      first_x_assum drule >> rw[] >>
      qpat_x_assum `step _ _` mp_tac >> rw[Once step_cases]
      >- (drule jumpTarget_eq >> rw[] >> gs[] >>
          fs[MEM] >> rw[]
          >- (`SUM (MAP sizeT (lamT::(P ⧺ [retT] ⧺ P''))) + 1 ≤ 2 * size s`
                by metis_tac[] >>
              fs[SUM, MAP, sizeT] >>
              `SUM (MAP sizeT P) + 1
                ≤ SUM (MAP sizeT P ⧺ [1] ⧺ MAP sizeT P'') + 2`
                by rw[SUM_APPEND] >>
              rw[integerTheory.INT_LE_TRANS])
          >> metis_tac[])
      >- (fs[put] >> rw[] >> metis_tac[])
      >- (drule lookup_el >> rw[] >>
          fs[] >> rw[] >> metis_tac[])
      >> fs[] >> metis_tac[])
    (* a ≤ LENGTH H *)
  >- (fs[ADD1] >> drule (iffLR pow_add) >> rw[] >>
      pop_assum mp_tac >> rw[Once rcomp] >>
      rename [`pow step 1 y (T',V,H)`] >>
      `step y (T', V, H)` by metis_tac[rcomp_1] >>
      PairCases_on `y` >> gs[] >>
      first_x_assum drule >> rw[] >>
      qpat_x_assum `step _ _` mp_tac >> rw[Once step_cases]
      >- (drule jumpTarget_eq >> rw[] >> gs[] >>
          fs[MEM] >> rw[] >> metis_tac[])
      >- (fs[put] >> rw[] >>
          `a ≤ LENGTH y2` by metis_tac[] >> rw[])
      >- (drule lookup_el >> rw[] >>
          fs[] >> rw[] >> metis_tac[])
      >> fs[] >> metis_tac[])
  (* MEM (heapEntryC (closC P a) beta) H *)
    (* SUM (MAP sizeT P) + 1 ≤ 2 * size s *)
  >- (fs[ADD1] >> drule (iffLR pow_add) >> rw[] >>
      pop_assum mp_tac >> rw[Once rcomp] >>
      rename [`pow step 1 y (T',V,H)`] >>
      `step y (T', V, H)` by metis_tac[rcomp_1] >>
      PairCases_on `y` >> gs[] >>
      first_x_assum drule >> rw[] >>
      qpat_x_assum `step _ _` mp_tac >> rw[Once step_cases]
      >- metis_tac[]
      >- (fs[put] >> rw[] >> fs[] >> metis_tac[])
      >- (drule lookup_el >> rw[] >>
          fs[] >> rw[] >> metis_tac[])
      >> fs[] >> metis_tac[])
    (* a ≤ LENGTH H *)
  >- (fs[ADD1] >> drule (iffLR pow_add) >> rw[] >>
      pop_assum mp_tac >> rw[Once rcomp] >>
      rename [`pow step 1 y (T',V,H)`] >>
      `step y (T', V, H)` by metis_tac[rcomp_1] >>
      PairCases_on `y` >> gs[] >>
      first_x_assum drule >> rw[] >>
      qpat_x_assum `step _ _` mp_tac >> rw[Once step_cases]
      >- metis_tac[]
      >- (fs[put] >> rw[] >> fs[] >> rw[]
          >- (`a ≤ LENGTH y2` by metis_tac[] >> rw[])
          >> `a ≤ LENGTH y2` by metis_tac[] >> rw[])
      >- (drule lookup_el >> rw[] >>
          fs[] >> rw[] >> metis_tac[])
      >> fs[] >> metis_tac[])
    (* beta ≤ LENGTH H *)
  >- (fs[ADD1] >> drule (iffLR pow_add) >> rw[] >>
      pop_assum mp_tac >> rw[Once rcomp] >>
      rename [`pow step 1 y (T',V,H)`] >>
      `step y (T', V, H)` by metis_tac[rcomp_1] >>
      PairCases_on `y` >> gs[] >>
      first_x_assum drule >> rw[] >>
      qpat_x_assum `step _ _` mp_tac >> rw[Once step_cases]
      >- metis_tac[]
      >- (fs[put] >> rw[] >> fs[] >> rw[]
          >- (`beta ≤ LENGTH y2` by metis_tac[] >> rw[])
          >> `b ≤ LENGTH y2` by metis_tac[] >> rw[])
      >- (drule lookup_el >> rw[] >>
          fs[] >> rw[] >> metis_tac[])
      >> fs[] >> metis_tac[])
QED

Theorem length_H:
  ∀i s T V H.
    pow step i (init s) (T,V,H) ⇒
    LENGTH H ≤ i
Proof
  Induct_on `i` >> rw[ADD1]
  >- (fs[pow, it_def, rcomp, init_def] >>
      drule (iffLR eq_cases) >> rw[])
  >> drule (iffLR pow_add) >> rw[] >>
  pop_assum mp_tac >> rw[Once rcomp] >>
  rename [`pow step 1 y (T',V,H)`] >>
  `step y (T', V, H)` by metis_tac[rcomp_1] >>
  PairCases_on `y` >> gs[] >>
  first_x_assum drule >> rw[] >>
  qpat_x_assum `step _ _` mp_tac >>
  rw[Once step_cases] >> rw[] >>
  fs[put] >> rw[]
QED

Theorem length_TV:
  ∀i s T V H.
    pow step i (init s) (T,V,H) ⇒
    LENGTH T + LENGTH V <= 1+i
Proof
  Induct_on `i` >> rw[ADD1]
  >- (fs[pow, it_def, rcomp, init_def] >>
      drule (iffLR eq_cases) >> rw[])
  >> drule (iffLR pow_add) >> rw[] >>
  pop_assum mp_tac >> rw[Once rcomp] >>
  rename [`pow step 1 y (T',V,H)`] >>
  `step y (T', V, H)` by metis_tac[rcomp_1] >>
  PairCases_on `y` >> gs[] >>
  first_x_assum drule >> rw[] >>
  qpat_x_assum `step _ _` mp_tac >>
  rw[Once step_cases] >> rw[] >>
  fs[put] >> rw[]
QED

Definition sizeC_def:
  sizeC g =
    case g of
      closC P a => sizeP P + a
End

Definition sizeHE_def:
  sizeHE e =
    case e of
      heapEntryC g b => sizeC g + b
End

Definition sizeH_def:
  sizeH H =
    SUM (MAP sizeHE H)
End

Definition sizeSt_def:
    sizeSt (Ts,V,H) =
      SUM (MAP sizeC Ts) + SUM (MAP sizeC V) + sizeH H
End

Theorem list_bound:
  ∀size m A.
    (∀x. MEM x A ⇒ size x ≤ m)
    ⇒ SUM (MAP size A) ≤ LENGTH A * m
Proof
  Induct_on `A` >> rw[] >>
  `∀x. MEM x A ⇒ size' x ≤ m` by metis_tac[] >>
  first_x_assum drule >> rw[] >>
  rw[ADD1] >>
  `size' h ≤ m` by metis_tac[] >>
  rw[integerTheory.INT_LDISTRIB]
QED

  (*
  Lemma list_bound X size m (A:list X):
    (forall x, x el A -> size x <= m) -> sum (map size A) <= length A * m.
  Proof.
    induction A;cbn;intros H'. omega.
    rewrite IHA. rewrite H'. omega. tauto. intuition.
  Qed.
  *)

Theorem correctSpace:
  ∀i s T V H.
    pow step i (init s) (T,V,H) ⇒
    sizeSt (T,V,H) ≤ (i + 1) * (3*i+4*size s)
Proof
  rw[sizeSt_def, sizeH_def] >>
  drule length_H >> rw[] >>
  drule length_TV >> rw[] >>
  `(∀x. MEM x T' ⇒ sizeC x ≤ (2*size s + i))
    ⇒ SUM (MAP sizeC T') ≤ LENGTH T' * (2*size s + i)`
    by metis_tac[list_bound] >>
  `(∀x. MEM x V ⇒ sizeC x ≤ (2*size s + i))
    ⇒ SUM (MAP sizeC V) ≤ LENGTH V * (2*size s + i)`
    by metis_tac[list_bound] >>
  `(∀x. MEM x H ⇒ sizeHE x ≤ (2*size s + 2*i))
    ⇒ SUM (MAP sizeHE H) ≤ LENGTH H * (2*size s + 2*i)`
    by metis_tac[list_bound] >>
  drule size_clos >> rw[] >>
  `∀x. MEM x T' ⇒ sizeC x ≤ 2 * size s + i`
    by (rw[] >> Cases_on `x` >>
        `sizeP l ≤ 2 * size s` by metis_tac[] >>
        rw[sizeC_def] >> rw[] >>
        `n ≤ LENGTH H` by metis_tac[] >>
        rw[]) >>
  first_x_assum drule >> rw[] >>
  `∀x. MEM x V ⇒ sizeC x ≤ 2 * size s + i`
    by (rw[] >> Cases_on `x` >>
        `sizeP l ≤ 2 * size s` by metis_tac[] >>
        rw[sizeC_def] >> rw[] >>
        `n ≤ LENGTH H` by metis_tac[] >>
        rw[]) >>
  first_x_assum drule >> rw[] >>
  `∀x. MEM x H ⇒ sizeHE x ≤ 2 * size s + 2 * i`
    by (rw[] >> Cases_on `x` >>
        rename [`MEM (heapEntryC c n) H`] >>
        Cases_on `c` >>
        rename [` MEM (heapEntryC (closC l n') n) H`] >>
        `sizeP l ≤ 2 * size s` by metis_tac[] >>
        rw[sizeHE_def] >> rw[] >>
        `n' ≤ LENGTH H` by metis_tac[] >>
        rw[sizeC_def] >> rw[] >>
        `n ≤ LENGTH H` by metis_tac[] >>
        rw[]) >>
  first_x_assum drule >> rw[] >>
  `SUM (MAP sizeC T') + SUM (MAP sizeC V) + SUM (MAP sizeHE H)
    ≤ LENGTH T' * (i + 2 * size s) + LENGTH V * (i + 2 * size s) +
      LENGTH H * (2 * i + 2 * size s)`
    by fs[] >>
  `(LENGTH T' + LENGTH V) * (i + 2 * size s) +
      LENGTH H * (2 * i + 2 * size s)
   ≤ (i + 1) * (2 * i + 2 * size s) + (i + 1) * (i + 2 * size s)`
    suffices_by rw[] >>
  qabbrev_tac `a = (LENGTH T' + LENGTH V) * (i + 2 * size s)` >>
  qabbrev_tac `b = LENGTH H * (2 * i + 2 * size s)` >>
  qabbrev_tac `c = (i + 1) * (i + 2 * size s)` >>
  qabbrev_tac `d = (i + 1) * (2 * i + 2 * size s)` >>
  `a + b ≤ c + d` suffices_by rw[] >>
  `a ≤ c ∧ b ≤ d` suffices_by rw[] >>
  rw[]
  >- rw[Abbr `a`, Abbr `c`]
  >> rw[Abbr `b`, Abbr `d`]
QED

(*
End Analysis.
*)

(* --------------------------------
    Bonus: Unfolding on Programs
   -------------------------------- *)
(*
Bonus: Unfolding on Programs
We define a function f to unfold a closure, needed for the Turing machine M_unf.
Section UnfoldPro.

  Variable H : list heapEntry.

  Fixpoint f (P:Pro) a k fuel {struct fuel}: option Pro :=
    match fuel with
      0 => None
    | S fuel =>
      match P,k with
       (* retT,0 => Some retT *)
      | retT::P,S k =>
        match f P a k fuel with
          Some P' => Some (retT::P')
        | _ => None
        end
      | appT::P,_ =>
        match f P a k fuel with
          Some P' => Some (appT::P')
        | _ => None
        end
      | lamT::P,_ =>
        match f P a (S k) fuel with
          Some P' => Some (lamT::P')
        | _ => None
        end
      | varT n::P,_ =>
        if Dec (n >= k) then
          match lookup H a (n-k) with
            Some (closC Q b) =>
            match f Q b 1 fuel,f P a k fuel with
              Some Q', Some P' =>
              Some (lamT::Q'++retT::P')
            | _,_ => None
            end
          | _ => None
          end
        else
          match f P a k fuel with
            Some P' =>
            Some (varT n::P')
          | _ => None
          end
      |[],_ => Some []
      |_,_ => None
      end
    end.

  Lemma f_mono P a k n n' :
    n <= n' -> f P a k n <> None -> f P a k n' = f P a k n.
  Proof.
    induction n in P,a,k,n'|-*. now cbn.
    destruct n'. now omega.
    intros leq eq. cbn in eq|-*.
    repeat (let eq := fresh "eq" in destruct _ eqn:eq).
    all:try congruence.
    all: repeat match goal with
            _ : S ?n <= S ?n',
                H : (f ?P ?a ?k ?n' = _) ,
                    H' : (f ?P ?a ?k ?n = _)
            |- _ => rewrite IHn in H;[ | omega | congruence]
                    end.
    all:congruence.
  Qed.
  Lemma f_correct' Q Q' a k s s' n:
    unfolds H a k s s' ->
    f Q a k n = Some Q' ->
    exists n', f (compile s++Q) a k n' = Some (compile s' ++ Q').
  Proof.
    induction s' in Q',Q,a,k,s,n |- *;intros H' eq.
    inv H'.
    - exists (S n). cbn. decide _. omega.
      now rewrite eq.
    - cbn. exfalso. inv H2. inv H3.
    - inv H'.
      {exfalso. inv H2. inv H3. }
      cbn [compile].
      autorewrite with list.
      edestruct IHs'2 with (Q:=appT::Q) (n:=S n) as [n2 eq2]. 1:eassumption.
      cbn. now rewrite eq.
      edestruct IHs'1 as [n1 eq1]. 1:eassumption.
      2:{
        eexists. erewrite eq1. reflexivity.
      }
      eassumption.
    -inv H'.
     +inv H2. inv H3.
      edestruct IHs' with (n:=1)(Q:=@nil Tok) as [n1 eq1]. eassumption.
      reflexivity.
      autorewrite with list in eq1.
      exists (S (max n n1)).
      cbn. decide _. 2:omega. rewrite H1. erewrite f_mono.
      rewrite eq1. erewrite f_mono. rewrite eq.
      autorewrite with list. reflexivity.
      1,3:now apply Nat.max_case_strong;omega.
      1-2:congruence.
     + cbn. edestruct IHs' as [n1 eq1].
       3:{eexists (S _).
       cbn.
       autorewrite with list.
       cbn. rewrite eq1. reflexivity. }
       eassumption.
       instantiate (1 := S n).
       cbn. rewrite eq. now destruct Q.
  Qed.
  Lemma f_correct a s s' k:
    unfolds H a k s s' ->
    exists n', f (compile s) a k n' = Some (compile s').
  Proof.
    intros H'.
    specialize (f_correct' (n:=1) (Q:=@nil Tok) (Q':=@nil Tok) H') as [n eq].
    reflexivity.
    autorewrite with list in eq.
    eexists. rewrite eq. reflexivity.
  Qed.
  Lemma f_correct_final P a s:
    reprC H (P!a) s ->
    exists t, s = lam t /\ exists n, f P a 1 n = Some (compile t).
  Proof.
    intros H'. inv H'. inv H4. inv H6.
    specialize (f_correct H2) as eq. eauto.
  Qed.
End UnfoldPro.

Lemma unfolds_inj H k s a s1 s2 :
  unfolds H k s a s1 -> unfolds H k s a s2 -> s1=s2.
Proof.
  induction 1 in s2|-*;intros H';inv H';try congruence;try omega.
  -apply IHunfolds.
   replace b with b0 in * by congruence.
   inv H2. inv H7.
   replace s1 with s in * by (apply compile_inj;congruence). tauto.
  -f_equal. apply IHunfolds. auto.
  -f_equal. all:auto.
Qed.
*)
val _ = export_theory ()