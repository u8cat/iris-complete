From stdpp Require Import gmultiset.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth excl gmultiset.
From iris.base_logic.lib Require Export own.

Class ghost_bagG Σ K `{Countable K} := Ghost_bagGS {
  #[local] ghost_bagGS_inG :: inG Σ (authUR (gmultisetO K));
}.

Definition ghost_bagΣ K `{Countable K} : gFunctors := #[GFunctor (authUR (gmultisetO K))].

Global Instance subG_ghost_bagG {Σ K} `{Countable K} : subG (ghost_bagΣ K) Σ → ghost_bagG Σ K.
Proof. solve_inG. Qed.

Section definitions.
  Context `{Countable K, !ghost_bagG Σ K}.

  Definition ghost_bag_auth γ (ks : gmultiset K) :=
    own γ (● ks).
  Definition ghost_bag_frag γ (k : K) : iProp Σ :=
    own γ (◯ {[+ k +]}).
End definitions.

Section theory.
  Context `{Countable K, !ghost_bagG Σ K}.

  Lemma ghost_bag_elem_of ks k γ :
    ghost_bag_auth γ ks -∗ ghost_bag_frag γ k -∗ ⌜k ∈ ks⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf")
      as %[?%gmultiset_included ?]%auth_both_valid_discrete.
    iPureIntro.
    multiset_solver.
  Qed.

  Lemma ghost_bag_update ks k k' γ :
    ghost_bag_auth γ ks -∗ ghost_bag_frag γ k ==∗
    ghost_bag_auth γ ({[+ k' +]} ⊎ ks ∖ {[+ k +]}) ∗ ghost_bag_frag γ k'.
  Proof.
    iIntros "Ha Hf".
    iDestruct (ghost_bag_elem_of with "Ha Hf") as %?.
    iMod (own_update_2 with "Ha Hf") as "[$ $]"; [|done].
    eapply auth_update, gmultiset_local_update.
    rewrite (gmultiset_disj_union_difference' k ks) //.
    multiset_solver.
  Qed.

  Lemma ghost_bag_insert k ks γ :
    ghost_bag_auth γ ks ==∗
    ghost_bag_auth γ ({[+ k +]} ⊎ ks) ∗ ghost_bag_frag γ k.
  Proof.
    iIntros "Ha".
    iMod (own_update with "Ha") as "[$ $]"; [|done].
    apply auth_update_alloc, gmultiset_local_update.
    multiset_solver.
  Qed.

  Lemma ghost_bag_insert_big ks' ks γ :
    ghost_bag_auth γ ks ==∗
    ghost_bag_auth γ (ks' ⊎ ks) ∗ [∗ mset] k∈ks', ghost_bag_frag γ k.
  Proof.
    iIntros "Ha".
    iMod (own_update γ _ ((● (ks'⊎ks)) ⋅ (◯ ks')) with "Ha") as "[$ Hf]".
    { apply auth_update_alloc, gmultiset_local_update. multiset_solver. }
    rewrite -[in own γ _](big_opMS_singletons ks') big_opMS_auth_frag.
    destruct (decide (ks' = ∅)) as [-> | ?].
    - rewrite big_sepMS_empty //.
    - rewrite -big_opMS_own //.
  Qed.

  Lemma ghost_bag_delete k ks γ :
    ghost_bag_auth γ ks ∗ ghost_bag_frag γ k ==∗
    ghost_bag_auth γ (ks ∖ {[+ k +]}).
  Proof.
    iIntros "[Ha Hf]".
    iDestruct (ghost_bag_elem_of with "Ha Hf") as %?.
    iMod (own_update_2 with "Ha Hf") as "$"; [|done].
    apply auth_update_dealloc, gmultiset_local_update.
    multiset_solver.
  Qed.

  Lemma ghost_bag_alloc_empty :
    ⊢ |==> ∃ γ, ghost_bag_auth γ ∅.
  Proof.
    iMod (own_alloc (● ∅)) as (γ) "$"; [|done].
    by apply auth_auth_valid.
  Qed.

  Lemma ghost_bag_alloc_big ks :
    ⊢ |==> ∃ γ, ghost_bag_auth γ ks ∗ [∗ mset] k ∈ ks, ghost_bag_frag γ k.
  Proof.
    iMod (own_alloc (● ks ⋅ [^op mset] k ∈ ks, ◯{[+ k +]})) as (γ) "[$ H◯]".
    { rewrite -big_opMS_auth_frag (big_opMS_singletons ks). by apply auth_both_valid. }
    destruct (decide (ks = ∅)) as [-> | ?].
    - rewrite big_sepMS_empty //.
    - rewrite big_opMS_own //.
  Qed.
End theory.
