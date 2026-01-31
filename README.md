# Complete Iris

This Rocq development shows the completeness of the [Iris](https://iris-project.org/) separation logic framework.

## Building the development

The project is known to compile with

- [Rocq](https://rocq-prover.org/) 9.1.0
- [std++](https://gitlab.mpi-sws.org/iris/stdpp) dev.2026-01-28.0.6f3f2617
- [Iris](https://gitlab.mpi-sws.org/iris/iris/) dev.2026-01-29.0.6cdf1efe

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
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam update
```
4. Install the right version of the dependencies as specified in the opam file.
```
opam install . --deps-only
```

You should now be able to build the development by using `make -j N` where `N` is the number of cores available on your machine.

## Main results

The completeness is shown semantically under the assumption that the base logic of Iris is complete. As Iris reasoning rules are modeled as entailments on weakest precondition assertions, the proof of completeness can be reduced to showing that a property about weakest precondition `WP`, i.e., the evaluation of expression `e` implies a `WP` of `e`. We phrase our results as a requisiteness theorem of `WP` (where word “requisiteness” is the duality of word “adequacy” used in the adequacy theorem).

```
Lemma wp_requisiteness_nofork e P Q :
  (∀ σ, P σ → adequate_nofork NotStuck e σ Q) →
  ⌞P⌟ ⊢ WP e {{ v, ⌞Q v⌟ }}.
...
Qed.
```

Here, `⌞P⌟` is the embedding of pure predicate `P` on state into separation logic. Intuitively, `⌞P⌟`  asserts the exclusive ownership of a fragment of the program state that satisfies `P`. This theorem forbids `e` to fork child threads.

We also have another theorem that allows forking but only works on a pure postcondition.

```
Lemma wp_requisiteness e P φ :
  (∀ σ, P σ → adequate NotStuck e σ (λ v _, φ v)) →
  ⌞P⌟ ⊢ WP e {{ v, ⌜φ v⌝ }}.
...
Qed.
```

Note that this theorem is false on a stateful postcondition:

```
(* False *)
Lemma wp_requisiteness' e P Q :
  (∀ σ, P σ → adequate NotStuck e σ Q) →
  ⌞P⌟ ⊢ WP e {{ v, ⌞Q v⌟ }}.
Abort.
```

This is because when the main thread terminates, it must frame a fragment of the state into resource `⌞Q v⌟` to conclude its postcondition, however, this will prevent child threads from accessing this part of the state that could be necessary for them to make progress.

## Discussion of theorem name

We invented a new term requisiteness because all candidate existing terms are problematic.

- **Completeness**. While this is a reasonable choice at first glimpse, it is technically wrong for the same reasoning that the adequacy theorem is called adequacy rather than soundness. While the overall goal is to show that the logic as a whole is complete, what we need here is a term for a property about `WP` rather than the whole logic. In fact, the notion of `WP` comes from denotational semantics, and indeed in Iris, `WP` is a denotation of an expression into `iProp`. In this sense, we need a term for “operational semantics implying denotational semantics“. Traditionally, the term completeness describes semantics implying syntax, but in our case, it is one semantics implying another. What's even worse is operational semantics looks more “syntactical” than denotational semantics. This also explains why Iris borrowed the term adequacy from denotational semantics instead of using soundness.
- **Full Abstraction**. This term is the duality of adequacy in the context of denotational semantics. However, full abstraction is a property about equivalence, therefore, it is weird to use it in a unary logic.
- **Necessity**. Think adequacy as strong enough so that it implies a good property. In terms of logical implication, the duality of adequacy should be a term for flipped implication, i.e., weak enough so that it is implied by the good property. In this sense, the quintessential term is necessity. However, necessity is traditionally paired with sufficiency, and we do not want to break this classic terms pair.

Why **requisiteness**? Term necessity is a good candidate with its only problem being paired with sufficiency. Therefore, we choose a synonym of necessity that is not traditionally paired with another term. Term requisiteness indeed captures the essence of our theorem—in order to have `adequate` held, `WP` is required to hold. The term also captures the fact that `WP` is indeed the *weakest* precondition—the precondition cannot be weaker because `WP` is required.
