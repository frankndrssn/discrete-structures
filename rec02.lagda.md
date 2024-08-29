# Propositional Logic

> :warning: Coding is **not** required for this class.
> You can safely ignore all code snippets in this document.

<details>
<summary>Code</summary>

```agda
{-# OPTIONS --safe #-}
module rec02 where
  open import prelude
  open import Agda.Builtin.Nat
```
</details>

Propositional logic consists of a language.
A language identifies a collection of symbols that can be used to form sentences and specifies those grammatical sentences.
For instance, the English language has 26 letters (52 if you include uppercase letters) plus puntuation symbols, and the grammar dictates that "I am Frank" is grammatical, while "I are Frank" is not. 

The language of propositional logic consists of *propositional variables*, and *logical symbols*: $\mathrm{T}$ (*top*), $\mathrm{F}$ (*bottom*), $\lnot$ (*negation*), $\land$ (*conjunction*), $\lor$ (*disjunction*), and $\implies$ (*implication*).
Propositional variables are intended to denote the basic things that we wish to discuss in propositional logic.

For example, perhaps I am interested in "is it raining" and "is it Wednesday".
I can include two propositional variables, "is-raining" and "is-wednesday", in the language to express these ideas.

## Syntax

*Propositions* are defined *inductively* as follows:
  - propositional variables are propositions
  - $\mathrm{T}$ and $\mathrm{F}$ are propositions
  - if $P$ is a proposition, then $\lnot P$ is a proposition
  - if $P$ and $Q$ are propositions, then $P \land Q$ is a proposition
  - if $P$ and $Q$ are propositions, then $P \lor Q$ is a proposition
  - if $P$ and $Q$ are propositions, then $P \implies Q$ is a proposition
  
By composing propositions with logical symbols, we can form more complicated propositions such as
```math
    \lnot\textrm{is-raining} \lor \textrm{is-wednesday} \implies \textrm{is-raining}
```

<details>
<summary>Code</summary>

```agda
  data 𝐏 : Type where
    ι : Nat → 𝐏
    ⊤ ⊥ : 𝐏
    ¬_ : 𝐏 → 𝐏
    _∧_ _∨_ _⇨_ : 𝐏 → 𝐏 → 𝐏
  infix 30 ¬_
  infixl 29 _∧_
  infixl 28 _∨_
  infixr 27 _⇨_
```
</details>

## Semantics

The string "Apfel" by itself does not mean anything, but we associate with it the round and usually red or green fruit (it means apple in German).
Similarly, propositions do not mean anything by themselves.
We are going to give each proposition a meaning by assigning to it a Boolean value.

Before we can discuss the semantics of propositional logic, we need to define a few Boolean functions.

### Not

The function $\mathrm{not}$ take a Boolean value and outputs a Boolean value.
It maps true to false and false to true.

| $b$   | $\mathrm{not}~b$ |
|-------|------------------|
| true  | false            |
| false | true             |

<details>
<summary>Code</summary>

```agda
  not : 𝔹 → 𝔹
  not true = false
  not false = true
```
</details>

### And

The function $\mathrm{and}$ takes two Boolean values and outputs true whenever both inputs are true, and outputs false otherwise.

| $a$   | $b$   | $a~\mathrm{and}~b$ |
|-------|-------|--------------------|
| true  | true  | true               |
| true  | false | false              |
| false | true  | false              |
| false | false | false              |

<details>
<summary>Code</summary>

```agda
  _and_ : 𝔹 → 𝔹 → 𝔹
  true and true = true
  true and false = false
  false and true = false
  false and false = false
```
</details>

### Or

The function $\mathrm{or}$ is dual to $\mathrm{and}$.
It takes two Boolean values and outputs false whenever both inputs are false, and outputs true otherwise.

| $a$   | $b$   | $a~\mathrm{or}~b$ |
|-------|-------|-------------------|
| true  | true  | true              |
| true  | false | true              |
| false | true  | true              |
| false | false | false             |

<details>
<summary>Code</summary>

```agda
  _or_ : 𝔹 → 𝔹 → 𝔹
  true or true = true
  true or false = true
  false or true = true
  false or false = false
```
</details>

### If ... then ...

The function $`\mathrm{if}~\ldots~\mathrm{then}~\ldots`$ also takes two Boolean values.
Its behaviour may seem somewhat strange.
You can think of it as a promise.
If a promises b but b does not happen, then a has broken his promise so the function outputs false.
On the other hand, if a does not promise b, then a cannot break his promise whether b happens or not, so the function outputs true for these cases.

| $a$   | $b$   | $`\mathrm{if}~a~\mathrm{then}~b`$ |
|-------|-------|-----------------------------------|
| true  | true  | true                              |
| true  | false | false                             |
| false | true  | true                              |
| false | false | true                              |

<details>
<summary>Code</summary>

```agda
  if_then_ : 𝔹 → 𝔹 → 𝔹
  if true then true = true
  if true then false = false
  if false then true = true
  if false then false = true

  _iff_ : 𝔹 → 𝔹 → 𝔹
  a iff b = (if a then b) and (if b then a)

  infix 30 not
  infixl 29 _and_
  infixl 28 _or_
  infixr 27 if_then_
  infix 26 _iff_
```
</details>

### Truth value assignments

With these Boolean functions in hand, we can finally assign meanings to propositions.
The intended meanings of the logical symbols are given in the table below:

| Logical symbol | Intended meaning |
|----------------|------------------|
| T              | true             |
| F              | false            |
| ¬              | not              |
| ∧              | and              |
| ∨              | or               |
| ⇨              | if ... then ...  |

<details>
<summary>Code</summary>

```agda
  tva : Type
  tva = Nat → 𝔹
```
</details>

Assigning meanings to propositional variables is where we have a bit more freedom.
We would assign true to is-raining on a rainy day, and false on a sunny day.
Similarly, we would assign true to is-wednesday on a Wednesday, and false on all other days.

Since there are 2 propositional variables, there are 4 possible *truth value assignments*.

|    | is-raining | is-wednesday |
|----|------------|--------------|
| 𝓜₁ | true       | true         |
| 𝓜₂ | true       | false        |
| 𝓜₃ | false      | true         |
| 𝓜₄ | false      | false        |

If the language has more propositional variables then there will be more truth value assignments.

Of course, the meaning of a proposition depends on which one of the 4 truth value assignments we are using.
Compound propositions can be assigned meanings systematically as follows:
- the meaning of $`\textrm{T}`$ in a given truth value assignment 𝓜 is true
- the meaning of $`\textrm{F}`$ in a given truth value assignment 𝓜 is false
- the meaning of $`\textrm{is-raining}`$ in a given truth value assignment 𝓜 is given by the truth value assignment 𝓜
- the meaning of $`\textrm{is-wednesday}`$ in a given truth value assignment 𝓜 is given by the truth value assignment 𝓜
- the meaning of $`\lnot P`$ in a given truth value assignment 𝓜 is given by applying the function $`\mathrm{not}`$ to the meaning of $P$ in the same truth value assignment 𝓜
- the meaning of $`P \land Q`$ in a given truth value assignment 𝓜 is given by applying the function $`\mathrm{and}`$ to the meanings of $P$ and $Q$ in the same truth value assignment 𝓜
- the meaning of $`P \lor Q`$ in a given truth value assignment 𝓜 is given by applying the function $`\mathrm{or}`$ to the meanings of $P$ and $Q$ in the same truth value assignment 𝓜
- the meaning of $`P \implies Q`$ in a given truth value assignment 𝓜 is given by applying the function $`\mathrm{if}~\ldots~\mathrm{then}~\ldots`$ to the meanings of $P$ and $Q$ in the same truth value assignment 𝓜

<details>
<summary>Code</summary>

```agda
  ⟦_⟧_ : 𝐏 → tva → 𝔹
  ⟦ ι x ⟧ 𝓜 = 𝓜 x
  ⟦ ⊤ ⟧ 𝓜 = true
  ⟦ ⊥ ⟧ 𝓜 = false
  ⟦ ¬ P ⟧ 𝓜 = not (⟦ P ⟧ 𝓜)
  ⟦ P ∧ Q ⟧ 𝓜 = (⟦ P ⟧ 𝓜) and (⟦ Q ⟧ 𝓜)
  ⟦ P ∨ Q ⟧ 𝓜 = (⟦ P ⟧ 𝓜) or (⟦ Q ⟧ 𝓜)
  ⟦ P ⇨ Q ⟧ 𝓜 = if (⟦ P ⟧ 𝓜) then (⟦ Q ⟧ 𝓜)
```
</details>

#### Examples

Let's evaluate $`\textrm{is-raining} \implies \textrm{is-wednesday}`$ in 𝓜₁.
- the meaning of $`\textrm{is-raining} \implies \textrm{is-wednesday}`$ in 𝓜₁\
	= $`\textrm{if}`$ (the meaning of $`\textrm{is-raining}`$ in 𝓜₁) $`\textrm{then}`$ (the meaning of $`\textrm{is-wednesday}`$ in 𝓜₁)\
	= $`\textrm{if}`$ true $`\textrm{then}`$ true\
	= true

Now, let's evaluate $`\textrm{is-raining} \implies \textrm{is-wednesday}`$ in 𝓜₃.
 - the meaning of $`\textrm{is-raining} \implies \textrm{is-wednesday}`$ in 𝓜₃\
     = $`\textrm{if}`$ (the meaning of $`\textrm{is-raining}`$ in 𝓜₃) $`\textrm{then}`$ (the meaning of $`\textrm{is-wednesday}`$ in 𝓜₃)\
     = $`\textrm{if}`$ false $`\textrm{then}`$ true\
     = false

This is expected since the weather does not dictate the day.
I have certainly had rainy days that were not on Wednesdays.

### Evaluating a general proposition

Arbitrary propositions $`P, Q, R`$, etc, can be assigned a Boolean value using the scheme described above.
These propositions can form more complicated propositions, such as $`(P \land Q) \implies R`$.
We use the same scheme to evaluate $`(P \land Q) \implies R`$.
For the sake of this example, suppose that $`P`$ and $`R`$ evaluate to true, and $`Q`$ evaluates to false in some truth value assignment 𝓜.
Then
- The meaning of $`(P \land Q) \implies R`$ in 𝓜\
  = $`\textrm{if}`$ (the meaning of $`P \land Q`$ in 𝓜) $`\textrm{then}`$ (the meaning of $`R`$ in 𝓜)\
  = $`\textrm{if}`$ (the meaning of $`P \land Q`$ in 𝓜) $`\textrm{then}`$ true\
  = $`\textrm{if}`$ ((the meaning of $`P`$ in 𝓜) $`\textrm{and}`$ (the meaning of $`\mathrm{Q}`$ in 𝓜)) $`\textrm{then}`$ true\
  = $`\textrm{if}`$ (true $`\textrm{and}`$ false) $`\textrm{then}`$ true\
  = $`\textrm{if}`$ false $`\textrm{then}`$ true\
  = true
  
Since a proposition evaluates to either true or false in any truth value assignment, we can exhaustively list all the possible values that $`(P \land Q) \implies R`$ takes with a *truth table*.

| $`P`$ | $`Q`$ | $`R`$ | $`(P \land Q) \implies R`$ |
|-------|-------|-------|----------------------------|
| true  | true  | true  | true                       |
| true  | true  | false | false                      |
| true  | false | true  | true                       |
| true  | false | false | true                       |
| false | true  | true  | true                       |
| false | true  | false | true                       |
| false | false | true  | true                       |
| false | false | false | true                       |

## Converse, contrapositive, inverse

Let $`P`$ and $`Q`$ be propositions.
The
- *converse* of $`P \implies Q`$ is the proposition $`Q \implies P`$.
- *contrapositive* of $`P \implies Q`$ is the proposition $`\lnot Q \implies \lnot P`$.
- *inverse* of $`P \implies Q`$ is the proposition $`\lnot P \implies \lnot Q`$.

### Example

The
- converse of $`\textrm{is-raining} \implies \textrm{is-wednesday}`$ is $`\textrm{is-wednesday} \implies \textrm{is-raining}`$.
- contrapositive of $`\textrm{is-raining} \implies \textrm{is-wednesday}`$ is $`\lnot \textrm{is-wednesday} \implies \lnot \textrm{is-raining}`$.
- inverse of $`\textrm{is-raining} \implies \textrm{is-wednesday}`$ is $`\lnot \textrm{is-raining} \implies \lnot \textrm{is-wednesday}`$.

## Tautologies

We just saw a proposition that is not true in every truth value assignment.
Let's evaluate $`\textrm{is-raining} \implies \textrm{is-raining}`$ in 𝓜₁ instead.
  - the meaning of $`\textrm{is-raining} \implies \textrm{is-raining}`$ in 𝓜₁\
       = $`\textrm{if}`$ (the meaning of $`\textrm{is-raining}`$ in 𝓜₁) $`\textrm{then}`$ (the meaning of $`\textrm{is-raining}`$ in 𝓜₁)\
       = $`\textrm{if}`$ true $`\textrm{then}`$ true\
       = true

Ok.
Let's evaluate it in 𝓜₃.
  - the meaning of $`\textrm{is-raining} \implies \textrm{is-raining}`$ in 𝓜₁\
       = $`\textrm{if}`$ (the meaning of $`\textrm{is-raining}`$ in 𝓜₁) $`\textrm{then}`$ (the meaning of $`\textrm{is-raining}`$ in 𝓜₁)\
       = $`\textrm{if}`$ false $`\textrm{then}`$ false\
       = true

It evaluates to true again.
In fact, this proposition evaluates to true in every truth value assignment.
This is expected because if it is raining, then of course it is raining.

Propositions that evaluate to true in all truth value assignments are called *tautologies*.
Let's see some examples.

<details>
<summary>Code</summary>

```agda
  data taut : 𝐏 → Type where
    tautK : {P : 𝐏} → ((𝓜 : tva) → ⟦ P ⟧ 𝓜 ≐ true) → taut P
```
</details>

### Identity

Let $`P`$ be any proposition.
We claim that $`P \implies P`$ is a tautology.
$`P`$ can evaluate to either true or false depending on the truth value assignment so there are two possibilities to check:

| $`P`$ | $`P \implies P`$ |
|-------|------------------|
| true  | true             |
| false | true             |

<details>
<summary>Code</summary>

```agda
  ⇨-id : {P : 𝐏} → taut (P ⇨ P)
  ⇨-id = tautK λ _ → ⇨-id' where
    ⇨-id' : {b : 𝔹} → if b then b ≐ true
    ⇨-id' {true} = ⋆
    ⇨-id' {false} = ⋆
```
</details>

### The law of excluded middle

Let $`P`$ be any proposition.
We claim that $`P \lor \lnot P`$ is a tautology.
Again, there are two possibilities to check:

| $`P`$ | $`P \lor \lnot P`$ |
|-------|--------------------|
| true  | true               |
| false | true               |

<details>
<summary>Code</summary>

```agda
  lem : {P : 𝐏} → taut (P ∨ ¬ P)
  lem = tautK (λ _ → lem') where
    lem' : {b : 𝔹} → b or (not b) ≐ true
    lem' {true} = ⋆
    lem' {false} = ⋆
```
</details>

### Distributive law

Let's try a more complicated example that involves more propositions.

Let $`P, Q`$, and $`R`$ be propositions.
We claim that $`P \land (Q \lor R) \implies ((P \land Q) \lor (P \land R))`$ is a tautology.
This time, we need to check 8 possibilities since every proposition can evaluate to either true or false depending on the truth value assignment.

| $`P`$ | $`Q`$ | $`R`$ | $`P \land (Q \lor R) \implies ((P \land Q) \lor (P \land R))`$ |
|-------|-------|-------|----------------------------------------------------------------|
| true  | true  | true  | true                                                           |
| true  | true  | false | true                                                           |
| true  | false | true  | true                                                           |
| true  | false | false | true                                                           |
| false | true  | true  | true                                                           |
| false | true  | false | true                                                           |
| false | false | true  | true                                                           |
| false | false | false | true                                                           |

<details>
<summary>Code</summary>

```agda
  distr : {P Q R : 𝐏} → taut (P ∧ (Q ∨ R) ⇨ (P ∧ Q) ∨ (P ∧ R))
  distr = tautK (λ _ → distr') where
    distr' : {a b c : 𝔹} → if (a and (b or c)) then ((a and b) or (a and c)) ≐ true
    distr' {true} {true} {true} = ⋆
    distr' {true} {true} {false} = ⋆
    distr' {true} {false} {true} = ⋆
    distr' {true} {false} {false} = ⋆
    distr' {false} {true} {true} = ⋆
    distr' {false} {true} {false} = ⋆
    distr' {false} {false} {true} = ⋆
    distr' {false} {false} {false} = ⋆
```
</details>

## Exercises

1. Evaluate the proposition $`\lnot (\lnot \textrm{is-raining}) \implies \textrm{is-raining}`$ in 𝓜₂ and 𝓜₄.
2. Let P be a proposition, is $`\lnot (\lnot P) \implies P`$ a tautology?
   Explain your answer.
3. Find a truth value assignment so that $`(\textrm{is-raining} \implies \textrm{is-wednesday}) \implies (\textrm{is-wednesday} \implies \textrm{is-raining})`$ does not evaluate to true. 
4. Let $`P`$ and $`Q`$ be propositions.
   Is $`(P \implies Q) \implies (Q \implies P)`$ a tautology?
   Explain your answer.
