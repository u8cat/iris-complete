# Complete Iris

This Rocq development shows the completeness of the [Iris](https://iris-project.org/) separation logic framework.

## Building the development

The project is known to compile with

- [Rocq](https://rocq-prover.org/) 9.0.1
- [std++](https://gitlab.mpi-sws.org/iris/stdpp) 1.12.0
- [Iris](https://gitlab.mpi-sws.org/iris/iris/) 4.4.0

The recommended way to install the dependencies is through [opam](https://opam.ocaml.org/doc/Install.html).

1. Install opam if not already installed (a version greater than 2.0 is required).
2. Install a new switch and link it to the project.
```
opam switch create iris-complete 5.3.0
opam switch link iris-complete .
```
3. Add the Rocq and Iris opam repositories.
```
opam repo add rocq-released https://rocq-prover.github.io/opam/released/
opam update
```
4. Install the right version of the dependencies as specified in the opam file.
```
opam install . --deps-only
```

You should now be able to build the development by using `make -j N` where `N` is the number of cores available on your machine.

## Main Results

The completeness is shown semantically under the assumption that the base logic of Iris is complete. As Iris reasoning rules are modeled as entailments on weakest precondition assertions, the completeness can be reduced to showing that a property about the evaluation of expression `e` implies a weakest precondition of `e`. We phrase our results as a requisiteness theorem of weakest precondition (where word “requisiteness” is the duality of word “adequacy” used in the adequacy theorem).

```
Theorem wp_requisiteness_nofork e (P : state → Prop) (Q : val → state → Prop) :
  (∀ σ, P σ → adequate_nofork NotStuck e σ Q) →
  ⌞P⌟ ⊢ WP e {{ v, ⌞Q v⌟ }}.
...
Qed.
```

Here, `⌞P⌟` is an embedding of a pure predicate on state into separation logic. Intuitively, `⌞P⌟`  declares the exclusive ownership of a fragment of the program state that satisfy `P`. This theorem forbids `e` to fork child threads.

We also have another theorem that allows fork but only talks about safety.

```
Notation safe_tp s t1 σ1 := (∀ t2 σ2 e2, s = NotStuck →
    rtc erased_step (t1, σ1) (t2, σ2) → e2 ∈ t2 → not_stuck e2 σ2).

Lemma wptp_safe t P :
  (∀ σ, P σ → safe_tp NotStuck t σ) →
  ⌞P⌟ ⊢ |={⊤}=> [∗ list] e ∈ t, WP e {{ _, True }}.
...
Qed.
```

Note that the combination of these two theorems is false:

```
(* False *)
Lemma wptp_requisiteness e t (P : state → Prop) (Q : val → state → Prop) :
  (∀ σ, P σ → adequate_tp NotStuck (e::t) σ Q) →
  ⌞P⌟ ⊢ |={⊤}=> WP e {{ v, ⌞Q v⌟ }} ∗ [∗ list] e ∈ t, WP e {{ _, True }}.
Abort.
```

This is because when the main thread terminates, it must frame a fragment of the state into resource `⌞Q v⌟` to conclude its postcondition, however, this will prevent child threads from accessing this part of the state that could be necessary for them to make progress.

## Discussion of theorem name

We invented a new term requisiteness because all candidate existing terms are problematic.

- **Completeness**. While this is a reasonable choice at first glimpse, it is technically wrong for the same reasoning that the adequacy theorem is called adequacy rather than soundness. While the overall goal is to show that the logic as a whole is complete, what we need here is a term for a property about weakest precondition rather than the whole logic. In fact, the notation of weakest precondition comes from denotational semantics, and indeed in Iris, the weakest precondition is a denotation of an expression into `iProp`. In this sense, we need a term for “operational semantics implying denotational semantics“. Traditionally, the term completeness describes semantics implying syntax, but in our case, it is one semantics implying another. What's even worse is operational semantics looks more “syntactical” than denotational semantics. This also explains why Iris borrowed the term adequacy from denotational semantics instead of using soundness.
- **Full Abstraction**. This term is the duality of adequacy in the context of denotational semantics. However, full abstraction is a property about equivalence, therefore, it is weird to use it in a unary logic.
- **Necessity**. Think adequacy as strong enough so that it implies a good property. In terms of logical implication, the duality of adequacy should be a term for flipped implication, i.e., weak enough so that it is implied by the good property. In this sense, the quintessential term is necessity. However, necessity is traditionally paired with sufficiency, and we do not want to break this classic terms pair.

Why **requisiteness**? Term necessity is a good candidate with its only problem being paired with sufficiency. Therefore, we choose a synonym of necessity that is not traditionally paired with another term. Term requisiteness indeed captures the essence of our theorem—in order to have `adequate_nofork` held, the `WP` is required to be held. The term also captures the fact that `WP` is indeed the *weakest* precondition—the precondition cannot be weaker because `WP` is required.
