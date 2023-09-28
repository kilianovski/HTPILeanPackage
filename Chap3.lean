import Chap3
namespace HTPI.Exercises
set_option pp.funBinderTypes true
set_option linter.unusedVariables false

theorem Example_3_2_4
    (P Q R : Prop) (h : P → (Q → R)) : ¬R → (P → ¬Q) := by
  assume hnr
  assume hp
  have qr := h hp
  contrapos at qr
  show ¬Q from qr hnr
  done

theorem Example_3_2_4_v2 (P Q R : Prop)
    (h : P → (Q → R)) : ¬R → (P → ¬Q) := by
  assume h2 : ¬R
  assume h3 : P
  by_contra hq
  have hr := (h h3) hq
  show False from h2 hr
  done

theorem Example_3_2_4_v3 (P Q R : Prop)
    (h : P → (Q → R)) : ¬R → (P → ¬Q) := by
  assume h2 : ¬R
  assume h3 : P
  by_contra h4
  contradict h2
  show R from  h h3 h4
  done

theorem Example_3_2_5_simple
    (U : Type)
    (B C : Set U) (a : U)
    (h1 : a ∈ B) (h2 : a ∉ B \ C) : a ∈ C := by
  define at h2
  demorgan at h2
  conditional at h2
  show a ∈ C from h2 h1
  done


theorem Example_3_2_5_simple_my
    (B C : Set Nat) (a : Nat)
    (h1 : a ∈ B) (h2 : a ∉ B \ C) : a ∈ C := by
  define at h2
  demorgan at h2
  show a ∈ C from h2.elim
    (fun h : a ∉ B => absurd h1 h)
    (fun h : a ∈ C => h)
  done

theorem Like_Example_3_2_5
    (U : Type) (A B C : Set U) (a : U)
    (h1 : a ∈ A) (h2 : a ∉ A \ B)
    (h3 : a ∈ B → a ∈ C) : a ∈ C := by

  define at h2
  demorgan at h2
  conditional at h2
  apply h3
  apply h2
  show a ∈ A from h1
  done


example (U : Type) (P Q : Pred U)
    (h1 : ∀ (x : U), P x → ¬Q x)
    (h2 : ∀ (x : U), Q x) :
    ¬∃ (x : U), P x := by
  quant_neg
  fix y
  have hpnq := h1 y

  contrapos at hpnq
  have hq := h2 y

  show ¬P y from hpnq hq
  done

example (U : Type) (A B C : Set U) (h1 : A ⊆ B ∪ C)
    (h2 : ∀ (x : U), x ∈ A → x ∉ B) : A ⊆ C := by

  define
  fix y
  assume ha
  define at h1

  have hnb := h2 y ha
  have hbc := h1 ha
  define at hbc
  conditional at hbc

  show y ∈ C from hbc hnb
  done

example (U : Type) (P Q : Pred U)
    (h1 : ∀ (x : U), ∃ (y : U), P x → ¬ Q y)
    (h2 : ∃ (x : U), ∀ (y : U), P x → Q y) :
    ∃ (x : U), ¬P x := by
  obtain (a : U) (h3 : ∀ (y : U), P a → Q y) from h2

  have h4 : (∃ (y : U), P a → ¬ Q y) := h1 a

  obtain (b : U) (h5 : P a → ¬ Q b) from h4
  have h6 := h3 b

  apply Exists.intro a
  by_contra h7

  show False from absurd (h6 h7) (h5 h7)
  done

theorem Example_3_3_5 (U : Type) (B : Set U)
    (F : Set (Set U)) : ⋃₀ F ⊆ B → F ⊆ 𝒫 B := by
    assume h : ⋃₀F ⊆ B
    define
    fix A : Set U
    assume hf : A ∈ F
    define
    fix y
    assume hya : y ∈ A
    define at h
    apply h
    define
    apply Exists.intro A
    show A ∈ F ∧ y ∈ A from ⟨hf, hya⟩

theorem Like_Example_3_4_1 (U : Type)
    (A B C D : Set U) (h1 : A ⊆ B)
    (h2 : ¬∃ (c : U), c ∈ C ∩ D) :
    A ∩ C ⊆ B \ D := by

  define
  fix x : U
  assume h3 : x ∈ A ∩ C
  define at h3; define
  apply And.intro
  ·
    define at h1
    show x ∈ B from h1 h3.left
    done

  ·
  -- contradict h with h' is shorthand for by_contra h'; contradict h.
    -- by_contra h2
    by_contra h4
    contradict h2
    apply Exists.intro x
    define
    -- contradict h2 with h4
    -- by_contra
    done
  
  done
