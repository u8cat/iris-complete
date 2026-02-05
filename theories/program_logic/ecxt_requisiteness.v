From iris.proofmode Require Import base ltac_tactics.
From iris.base_logic Require Import ghost_map invariants.
From iris.program_logic Require Export ectx_lifting.
From complete_iris.program_logic Require Export requisiteness.

Class ectx_coirisG_gen (hlc : has_lc) (Λ : ectxLanguage) (Σ: gFunctors) `{!irisGS_gen hlc Λ Σ} := EctxCoirisG {
  state_empty : state Λ;

  own_state : state Λ → nat → list (observation Λ) → nat → iProp Σ;
  #[local] own_state_timeless σ ns κ nt :: Timeless (own_state σ ns κ nt);

  fork_post_trivial v : ⊢ fork_post v;

  own_state_empty ns κs nt : ⊢ own_state state_empty ns κs nt;

  own_state_update e σ ns κ κs nt σl ns' κ' nt' :
    base_reducible e σl →
    state_interp σ ns (κ++κs) nt -∗ own_state σl ns' κ' nt' -∗
    ⌜base_reducible e σ⌝ ∗
    (∀ e' σ' efs, ⌜base_step e σ κ e' σ' efs⌝ ={∅}=∗
    ∃ σl', ⌜base_step e σl κ e' σl' efs⌝ ∗ state_interp σ' (S ns) κs (length efs + nt) ∗ own_state σl' (S ns) κs (length efs + nt));
}.
Global Arguments EctxCoirisG {hlc Λ Σ _}.

Notation ectx_coirisG Λ Σ := (ectx_coirisG_gen HasLc Λ Σ).

Class requisiteG Λ Σ := RequisiteG {
  #[local] requisiteG_bag :: ghost_mapG Σ nat (expr Λ * (val Λ → Prop));
}.

Global Program Instance ectx_coirisG_coirisG hlc (Λ : ectxLanguage) Σ `{!irisGS_gen hlc Λ Σ,
  !ectx_coirisG_gen hlc Λ Σ} : coirisG_gen hlc Λ Σ := {
  state_empty := state_empty;
  own_state := own_state;
  fork_post_trivial := fork_post_trivial;
  own_state_empty := own_state_empty;
}.
Next Obligation.
  iIntros (hlc Λ Σ ?? e σ ns κ κs nt σl ns' κ' nt' Hred) "H● H◯".
  destruct Hred as (κ2 & e2 & σ2 & efs & Hprim_stepl). simpl in *.
  destruct Hprim_stepl as [K e_ e2_ -> -> Hbase_stepl]. simpl in *.
  iDestruct (own_state_update with "H● H◯") as "[%Hredl Hupdate]".
  { do 4 eexists; eassumption. }
  iSplit; first auto using base_prim_fill_reducible.
  iIntros (e' σ' efs' Hprim_step).
  apply base_reducible_prim_step_ctx in Hprim_step; last assumption.
  destruct Hprim_step as (e2' & -> & Hbase_step).
  iMod ("Hupdate" with "[//]") as (σl') "(%Hbase_step' & $ & $)".
  iPureIntro.
  by econstructor.
Qed.
