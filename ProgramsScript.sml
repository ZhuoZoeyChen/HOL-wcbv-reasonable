open HolKernel Parse boolLib bossLib;
open arithmeticTheory;
open listTheory;
open PrelimsTheory;
open LTheory;

val _ = new_theory "Programs";

(* --------------------------------
      Encoding Terms as Programs
   -------------------------------- *)

Datatype:
  Tok = varT num | appT | lamT | retT
End

Type Pro = ``:Tok list``;

(* compilation function : Ter → Pro
    translates terms into programs: *)
Definition compile:
  compile s =
    case s of
      | var x => [varT x]
      | app s t => compile s ++ compile t ++ [appT]
      | lam s => lamT::compile s ++ [retT]
End

Inductive reprP:
[~PC:]
  (∀s. reprP (compile s) (lam s))
End

(* --------------------
      Program Size
   -------------------- *)

(* sum := SUM *)
(* sum_app := SUM_APPEND *)

Definition sizeT:
  sizeT t =
    case t of
      | varT n => 1 + n
      | _ => 1
End

Definition sizeP:
  sizeP P = SUM (MAP sizeT P) + 1
End

Theorem size_geq_1:
  ∀s. 1 ≤ size s
Proof
  Induct_on `s` >> rw[Once size]
QED

Theorem sizeP_size':
  ∀s. size s ≤ SUM (MAP sizeT (compile s))
Proof
  Induct_on `s` >> rw[]
  >- rw[Once size, sizeT, compile]
  >- (rw[Once size, Once compile, Once sizeT] >>
      rw[SUM_APPEND])
  >> rw[Once size, Once compile, Once sizeT] >>
  rw[Once sizeT] >> rw[SUM_APPEND]
QED

Theorem sizeP_size:
  ∀s. SUM (MAP sizeT (compile s)) + 1 ≤ 2*size s
Proof
  Induct_on `s` >> rw[]
  >- rw[Once compile, Once sizeT, Once size]
  >- rw[Once compile, Once sizeT, Once size, SUM_APPEND]
  >> rw[Once compile, Once sizeT, Once size] >>
  rw[Once sizeT] >> rw[SUM_APPEND]
QED

(* ------------------------------
       Program Decomposition
   ------------------------------ *)

(* extracts the body of an abstraction *)
Definition jumpTarget:
  jumpTarget l res P =
    case P of
      | retT :: P => (case l of
                       | 0 => SOME (res, P)
                       | SUC l => jumpTarget l (res++[retT]) P)
      | lamT :: P => jumpTarget (SUC l) (res++[lamT]) P
      | t :: P => jumpTarget l (res++[t]) P
      | [] => NONE
End

Theorem jumpTarget_correct':
  ∀k l s lst. jumpTarget k lst (compile s ++ l) = jumpTarget k (lst++compile s) l
Proof
  Induct_on `s` >> rw[]
  >- (rw[Once compile] >> rw[Once compile] >>
      rw[Once jumpTarget])
  >- (rw[Once compile] >> simp[SimpR ``$=``, Once compile] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpTarget])
  >> rw[Once compile] >> simp[SimpR ``$=``, Once compile] >>
  rw[Once jumpTarget] >>
  FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
  rw[Once jumpTarget] >>
  FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND]
QED

Theorem jumpTarget_correct:
  ∀s c. jumpTarget 0 [] (compile s ++ retT::c) = SOME (compile s, c)
Proof
  rw[] >>
  `SOME (compile s, c) = jumpTarget 0 ([]++compile s) (retT::c)` by rw[jumpTarget] >>
  metis_tac[jumpTarget_correct']
QED

Theorem jumpTarget_correct_conc:
  ∀s c. jumpTarget 0 [] (compile s ++ [retT] ++ c) = SOME (compile s, c)
Proof
  rw[] >>
  `jumpTarget 0 [] (compile s ++ retT::c) = SOME (compile s, c)`
    by rw[jumpTarget_correct] >>
  `compile s ⧺ [retT] ⧺ c = compile s ⧺ retT::c`
    suffices_by metis_tac[] >>
  rw[rich_listTheory.CONS_APPEND]
QED

(* ------------------------------
       Programm Substitution
   ------------------------------ *)


Definition substP:
  substP P k Q =
    case P of
    | [] => []
    | lamT::P => lamT::substP P (SUC k) Q
    | retT::P => (retT::(case k of
                          | SUC k => substP P k Q
                          | 0 => [varT 42 (* doesnt matter *)]))
    | varT k'::P => ((if (k'=k) then Q else [varT k'])++substP P k Q)
    | appT::P => appT::substP P k Q
End

Theorem substP_correct':
  ∀s k c' t.
    substP (compile s++c') k (compile t)
    = compile (subst s k t)++substP c' k (compile t)
Proof
  Induct_on `s` >> rw[]
  >- (rw[Once compile, Once substP, Once subst] >>
      rw[Once compile])
  >- (rw[Once compile, Once subst] >>
      simp[SimpR ``$=``, Once compile] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once substP])
  >> rw[Once compile, Once subst] >>
  simp[SimpR ``$=``, Once compile] >>
  rw[Once substP] >>
  FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
  rw[Once substP]
QED

Theorem substP_correct:
  ∀s k t.
    substP (compile s) k (compile t) = compile (subst s k t)
Proof
  `∀s k t. substP (compile s++[]) k (compile t) = compile (subst s k t)++substP [] k (compile t)`
    suffices_by (rw[] >> simp[Once substP]) >>
  metis_tac[substP_correct']
QED

(* -------------------------------------------
       Injectivity of Programm Encoding
   -------------------------------------------*)

(* decompilation function
    translates programs into terms *)
Definition decompile:
  decompile l P A =
    case P of
    | retT::P => (case l of
                  | 0 => NONE
                  | SUC l => (case A of
                              | s::A => decompile l P (lam s::A)
                              | [] => NONE))
    | varT n::P => decompile l P (var n::A)
    | lamT::P => decompile (SUC l) P A
    | appT::P => (case A of
                  | t::s::A => decompile l P (app s t::A)
                  | _ => NONE)
    | [] => SOME A
End

Theorem decompile_correct':
  ∀l s P A.
    decompile l (compile s++P) A = decompile l P (s::A)
Proof
  Induct_on `s` >> rw[]
  >- (rw[Once compile, Once decompile])
  >- (rw[Once compile] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once decompile])
  >> rw[Once compile] >>
  rw[Once decompile] >>
  FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
  rw[Once decompile]
QED

Theorem compile_inj:
  ∀s s'.
    compile s = compile s' ⇒ s = s'
Proof
  rw[] >>
  `decompile 0 (compile s++[]) [] = decompile 0 [] (s::[])`
    by metis_tac[decompile_correct'] >>
  `decompile 0 (compile s'++[]) [] = decompile 0 [] (s'::[])`
    by metis_tac[decompile_correct'] >>
  gs[] >> fs[Once decompile] >> fs[Once decompile]
QED

val _ = export_theory ()