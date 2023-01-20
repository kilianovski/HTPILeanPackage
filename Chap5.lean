import HTPIDefs
namespace HTPI
set_option pp.funBinderTypes true

--From Chapter 4
def inv {A B : Type} (R : Set (A × B)) : Set (B × A) :=
    { (b, a) : B × A | (a, b) ∈ R }
def comp {A B C : Type} (S : Set (B × C)) (R : Set (A × B)) :
    Set (A × C) := { (a, c) : A × C | ∃ (x : B), (a, x) ∈ R ∧ (x, c) ∈ S }
theorem simp_inv {A B : Type} (R : Set (A × B)) (a : A) (b : B) :
    (b, a) ∈ inv R ↔ (a, b) ∈ R := by rfl
def sub (A : Type) (X Y : Set A) : Prop := X ⊆ Y
def smallestElt {A : Type} (R : BinRel A) (b : A) (B : Set A) : Prop :=
    b ∈ B ∧ ∀ x ∈ B, R b x

--Chapter 5
--5.1
/- This definition is in HTPIDefs
def graph {A B : Type} (f : A → B) : Set (A × B) :=
    { (a, b) : A × B | f a = b }
-/

theorem simp_graph {A B : Type} (f : A → B) (a : A) (b : B) :
    (a, b) ∈ graph f ↔ f a = b := by rfl

/- Also in HTPIDefs
def is_func_graph {A B : Type} (F : Set (A × B)) : Prop :=
    ∀ (x : A), ∃! (y : B), (x, y) ∈ F
theorem func_from_graph {A B : Type} (F : Set (A × B)) :
    (∃ (f : A → B), graph f = F) ↔ is_func_graph F
-/

theorem Theorem_5_1_4 {A B : Type} (f g : A → B) :
    (∀ (a : A), f a = g a) → f = g := funext

example {A B : Type} (f g : A → B) :
    graph f = graph g → f = g := by
  assume h1 : graph f = graph g  --Goal: f = g
  apply funext                   --Goal: ∀ (x : A), f x = g x
  fix x : A
  have h2 : (x, f x) ∈ graph f := by
    define                       --Goal: f x = f x
    rfl
    done
  rewrite [h1] at h2             --h2: (x, f x) ∈ graph g
  define at h2                   --h2: g x = f x
  show f x = g x from h2.symm
  done

def square1 (n : Nat) : Nat := n^2
def square2 : Nat → Nat := fun (n : Nat) => n^2

example : square1 = square2 := by rfl
example : square1 7 = 49 := by rfl

theorem Theorem_5_1_5 {A B C : Type} (f : A → B) (g : B → C) :
    ∃ (h : A → C), graph h = comp (graph g) (graph f) := by
  let h : A → C := fun (x : A) => g (f x)
  apply Exists.intro h
  apply Set.ext
  fix (a, c) : A × C
  apply Iff.intro
  · -- Proof that (a, c) ∈ graph h → (a, c) ∈ comp (graph g) (graph f)
    assume h1 : (a, c) ∈ graph h
    define at h1  --h1: h a = c
    define        --Goal:  ∃ (x : B), (a, x) ∈ graph f ∧ (x, c) ∈ graph g
    apply Exists.intro (f a)
    apply And.intro
    · -- Proof that (a, f a) ∈ graph f
      define
      rfl
      done
    · -- Proof that (f a, c) ∈ graph g
      define
      show g (f a) = c from h1
      done
    done
  · -- Proof that (a, c) ∈ comp (graph g) (graph f) → (a, c) ∈ graph h
    assume h1 : (a, c) ∈ comp (graph g) (graph f)
    define        --Goal: h a = c
    define at h1  --h1: ∃ (x : B), (a, x) ∈ graph f ∧ (x, c) ∈ graph g
    obtain (b : B) (h2 : (a, b) ∈ graph f ∧ (b, c) ∈ graph g) from h1
    have h3 : (a, b) ∈ graph f := h2.left
    have h4 : (b, c) ∈ graph g := h2.right
    define at h3          --h3: f a = b
    define at h4          --h4: g b = c
    rewrite [←h3] at h4   --h4: g (f a) = c
    show h a = c from h4
    done
  done

example {A B C D : Type} (f : A → B) (g : B → C) (h : C → D) :
    h ∘ (g ∘ f) = (h ∘ g) ∘ f := by rfl

example {A B : Type} (f : A → B) : f ∘ id = f := by rfl
example {A B : Type} (f : A → B) : id ∘ f = f := by rfl

-- 5.2
def onto {A B : Type} (f : A → B) : Prop :=
  ∀ (y : B), ∃ (x : A), f x = y
def one_to_one {A B : Type} (f : A → B) : Prop :=
  ∀ (x1 x2 : A), f x1 = f x2 → x1 = x2

theorem Theorem_5_2_5_1 {A B C : Type} (f : A → B) (g : B → C) :
    one_to_one f → one_to_one g → one_to_one (g ∘ f) := by
  assume h1 : one_to_one f
  assume h2 : one_to_one g
  define at h1  --h1: ∀ (x1 x2 : A), f x1 = f x2 → x1 = x2
  define at h2  --h2: ∀ (x1 x2 : B), g x1 = g x2 → x1 = x2
  define        --Goal: ∀ (x1 x2 : A), (g ∘ f) x1 = (g ∘ f) x2 → x1 = x2
  fix a1 : A
  fix a2 : A    --Goal: (g ∘ f) a1 = (g ∘ f) a2 → a1 = a2
  define : (g ∘ f) a1; define : (g ∘ f) a2
                --Goal: g (f a1) = g (f a2) → a1 = a2
  assume h3 : g (f a1) = g (f a2)
  have h4 : f a1 = f a2 := h2 (f a1) (f a2) h3
  show a1 = a2 from h1 a1 a2 h4
  done

theorem Theorem_5_2_5_2 {A B C : Type} (f : A → B) (g : B → C) :
    onto f → onto g → onto (g ∘ f) := by
  assume h1 : onto f
  assume h2 : onto g
  define at h1           --h1: ∀ (y : B), ∃ (x : A), f x = y
  define at h2           --h2: ∀ (y : C), ∃ (x : B), g x = y
  define                 --Goal: ∀ (y : C), ∃ (x : A), (g ∘ f) x = y
  fix c : C
  obtain (b : B) (h3 : g b = c) from h2 c
  obtain (a : A) (h4 : f a = b) from h1 b
  apply Exists.intro a   --Goal: (g ∘ f) a = c
  define : (g ∘ f) a     --Goal: g (f a) = c
  rewrite [←h4] at h3
  show g (f a) = c from h3
  done

-- 5.3
#check @func_from_graph

theorem Theorem_5_3_1 {A B : Type}
    (f : A → B) (h1 : one_to_one f) (h2 : onto f) :
    ∃ (g : B → A), graph g = inv (graph f) := by
  apply (func_from_graph (inv (graph f))).rtl
                --Goal: is_func_graph (inv (graph f))
  define        --Goal: ∀ (x : B), ∃! (y : A), (x, y) ∈ inv (graph f)
  fix b : B
  exists_unique
  · -- Existence
    define at h2          --h2: ∀ (y : B), ∃ (x : A), f x = y
    obtain (a : A) (h4 : f a = b) from h2 b
    apply Exists.intro a  --Goal: (b, a) ∈ inv (graph f)
    define                --Goal: f a = b
    show f a = b from h4
    done
  · -- Uniqueness
    fix a1 : A; fix a2 : A
    assume h3 : (b, a1) ∈ inv (graph f)
    assume h4 : (b, a2) ∈ inv (graph f) --Goal: a1 = a2
    define at h3          --h3: f a1 = b
    define at h4          --h4: f a2 = b
    rewrite [←h4] at h3   --h3: f a1 = f a2
    define at h1          --h1: ∀ (x1 x2 : A), f x1 = f x2 → x1 = x2
    show a1 = a2 from h1 a1 a2 h3
    done
  done

theorem Theorem_5_3_2_1 {A B : Type} (f : A → B) (g : B → A)
    (h1 : graph g = inv (graph f)) : g ∘ f = id := by
  apply funext           --Goal: ∀ (x : A), (g ∘ f) x = id x
  fix a : A              --Goal: (g ∘ f) a = id a
  have h2 : (f a, a) ∈ graph g := by
    rewrite [h1]         --Goal: (f a, a) ∈ inv (graph f)
    define               --Goal:  f a = f a
    rfl
    done
  define at h2           --h2: g (f a) = a
  show (g ∘ f) a = id a from h2
  done

theorem Theorem_5_3_2_2 {A B : Type} (f : A → B) (g : B → A)
    (h1 : graph g = inv (graph f)) : f ∘ g = id := sorry

theorem Theorem_5_3_3_1 {A B : Type} (f : A → B) :
    (∃ (g : B → A), g ∘ f = id) → one_to_one f := by
  assume h1 : ∃ (g : B → A), g ∘ f = id
  obtain (g : B → A) (h2 : g ∘ f = id) from h1
  define              --Goal: ∀ (x1 x2 : A), f x1 = f x2 → x1 = x2
  fix a1 : A; fix a2 : A
  assume h3 : f a1 = f a2
  show a1 = a2 from
    calc a1
        = id a1 := by rfl
      _ = (g ∘ f) a1 := by rw [h2]
      _ = g (f a1) := by rfl
      _ = g (f a2) := by rw [h3]
      _ = (g ∘ f) a2 := by rfl
      _ = id a2 := by rw [h2]
      _ = a2 := by rfl
  done

theorem Theorem_5_3_3_2 {A B : Type} (f : A → B) :
    (∃ (g : B → A), f ∘ g = id) → onto f := sorry

theorem Theorem_5_3_5 {A B : Type} (f : A → B) (g : B → A)
    (h1 : g ∘ f = id) (h2 : f ∘ g = id) : graph g = inv (graph f) := by
  have h3 : one_to_one f := Theorem_5_3_3_1 f (Exists.intro g h1)
  have h4 : onto f := Theorem_5_3_3_2 f (Exists.intro g h2)
  obtain (g' : B → A) (h5 : graph g' = inv (graph f))
    from Theorem_5_3_1 f h3 h4
  have h6 : g' ∘ f = id := Theorem_5_3_2_1 f g' h5
  have h7 : g = g' :=
    calc g
        = id ∘ g := by rfl
      _ = (g' ∘ f) ∘ g := by rw [h6]
      _ = g' ∘ (f ∘ g) := by rfl
      _ = g' ∘ id := by rw [h2]
      _ = g' := by rfl
  rewrite [←h7] at h5
  show graph g = inv (graph f) from h5
  done

-- 5.4
def closed {A : Type} (f : A → A) (C : Set A) : Prop := ∀ x ∈ C, f x ∈ C

def closure {A : Type} (f : A → A) (B C : Set A) : Prop :=
    smallestElt (sub A) C { D : Set A | B ⊆ D ∧ closed f D}

theorem Theorem_5_4_5 {A : Type} (f : A → A) (B : Set A) :
    ∃ (C : Set A), closure f B C := by
  let F : Set (Set A) := { D : Set A | B ⊆ D ∧ closed f D }
  let C : Set A := ⋂₀F
  apply Exists.intro C    --Goal: closure f B C
  define                  --Goal: C ∈ F ∧ ∀ x ∈ F, C ⊆ x
  apply And.intro
  · -- Proof that C ∈ F
    define                  --Goal: B ⊆ C ∧ closed f C
    apply And.intro
    · -- Proof that B ⊆ C
      fix a : A
      assume h1 : a ∈ B       --Goal: a ∈ C
      define                  --Goal: ∀ t ∈ F, a ∈ t
      fix D : Set A
      assume h2 : D ∈ F
      define at h2            --h2: B ⊆ D ∧ closed f D
      show a ∈ D from h2.left h1
      done
    · -- Proof that C is closed under f
      define                  --Goal: ∀ x ∈ C, f x ∈ C
      fix a : A
      assume h1 : a ∈ C       --Goal: f a ∈ C
      define                  --Goal: ∀ t ∈ F, f a ∈ t
      fix D : Set A
      assume h2 : D ∈ F       --Goal: f a ∈ D
      define at h1            --h1: ∀ t ∈ F, a ∈ t
      have h3 : a ∈ D := h1 D h2
      define at h2            --h2: B ⊆ D ∧ closed f D
      have h4 : closed f D := h2.right
      define at h4            --h4: ∀ x ∈ D, f x ∈ D
      show f a ∈ D from h4 a h3
      done
    done
  · -- Proof that C is smallest
    fix D : Set A
    assume h1 : D ∈ F      --Goal: sub A C D
    define
    fix a : A
    assume h2 : a ∈ C       --Goal: a ∈ D
    define at h2            --h2: ∀ t ∈ F, a ∈ t
    show a ∈ D from h2 D h1
    done
  done

def plus (m n : Int) : Int := m + n
def plus' : Int → Int → Int := fun (m n : Int) => m + n
def plus'' : Int → Int → Int := fun (m : Int) => (fun (n : Int) => m + n)

example : plus = plus'' := by rfl
example : plus' = plus'' := by rfl
example : plus 3 2 = 5 := by rfl

#check plus
#check plus'
#check plus''

def closed2 {A : Type} (f : A → A → A) (C : Set A) : Prop :=
    ∀ x ∈ C, ∀ y ∈ C, f x y ∈ C
def closure2 {A : Type} (f : A → A → A) (B C : Set A) : Prop := 
    smallestElt (sub A) C { D : Set A | B ⊆ D ∧ closed2 f D }

theorem Theorem_5_4_9 {A : Type} (f : A → A → A) (B : Set A) :
    ∃ (C : Set A), closure2 f B C := sorry

-- 5.5
def image {A B : Type} (f : A → B) (X : Set A) : Set B :=
    { f x | x ∈ X }
def inverse_image {A B : Type} (f : A → B) (Y : Set B) : Set A :=
    { a : A | f a ∈ Y }
-- The following theorems illustrate the meaning of these definitions:
theorem simp_image {A B : Type} (f : A → B) (X : Set A) (b : B) :
    b ∈ image f X ↔ ∃ x ∈ X, f x = b := by rfl
theorem simp_inverse_image {A B : Type} (f : A → B) (Y : Set B) (a : A) :
    a ∈ inverse_image f Y ↔ f a ∈ Y := by rfl

theorem Theorem_5_5_2_1 {A B : Type} (f : A → B) (W X : Set A) :
    image f (W ∩ X) ⊆ image f W ∩ image f X := by
  fix y : B
  assume h1 : y ∈ image f (W ∩ X)  --Goal: y ∈ image f W ∩ image f X
  define at h1                     --h1: ∃ (x : A), x ∈ W ∩ X ∧ f x = y
  obtain (x : A) (h2 : x ∈ W ∩ X ∧ f x = y) from h1
  define : x ∈ W ∩ X at h2         --h2: (x ∈ W ∧ x ∈ X) ∧ f x = y
  apply And.intro
  · -- Proof that y ∈ image f W
    define                           --Goal: ∃ (x : A), x ∈ W ∧ f x = y
    show ∃ (x : A), x ∈ W ∧ f x = y from
      Exists.intro x (And.intro h2.left.left h2.right)
    done
  · -- Proof that y ∈ image f X
    show y ∈ image f X from
      Exists.intro x (And.intro h2.left.right h2.right)
    done
  done

theorem Theorem_5_5_2_2 {A B : Type} (f : A → B) (W X : Set A)
    (h1 : one_to_one f) : image f (W ∩ X) = image f W ∩ image f X := by
  apply Set.ext
  fix y : B      --Goal: y ∈ image f (W ∩ X) ↔ y ∈ image f W ∩ image f X
  apply Iff.intro
  · -- (→)
    assume h2 : y ∈ image f (W ∩ X)
    show y ∈ image f W ∩ image f X from Theorem_5_5_2_1 f W X h2
    done
  · -- (←)
    assume h2 : y ∈ image f W ∩ image f X  --Goal: y ∈ image f (W ∩ X)
    define at h2                  --h2: y ∈ image f W ∧ y ∈ image f X
    rewrite [simp_image, simp_image] at h2
          --h2: (∃ (x : A), x ∈ W ∧ f x = y) ∧ ∃ (x : A), x ∈ X ∧ f x = y
    obtain (x1 : A) (h3 : x1 ∈ W ∧ f x1 = y) from h2.left
    obtain (x2 : A) (h4 : x2 ∈ X ∧ f x2 = y) from h2.right
    have h5 : f x2 = y := h4.right
    rewrite [←h3.right] at h5    --h5: f x2 = f x1
    define at h1                 --h1: ∀ (x1 x2 : A), f x1 = f x2 → x1 = x2
    have h6 : x2 = x1 := h1 x2 x1 h5
    rewrite [h6] at h4           --h4: x1 ∈ X ∧ f x1 = y
    show y ∈ image f (W ∩ X) from
      Exists.intro x1 (And.intro (And.intro h3.left h4.left) h3.right)
    done
  done

example {A B : Type} (f : A → B) (W X : Set A) :
    image f (W ∪ X) = image f W ∪ image f X := sorry

example {A B : Type} (f : A → B) (W X : Set A) :
    image f (W \ X) = image f W \ image f X := sorry

example {A B : Type} (f : A → B) (W X : Set A) :
    W ⊆ X ↔ image f W ⊆ image f X := sorry

example {A B : Type} (f : A → B) (Y Z : Set B) :
    inverse_image f  (Y ∩ Z) =
        inverse_image f Y ∩ inverse_image f Z := sorry

example {A B : Type} (f : A → B) (Y Z : Set B) :
    inverse_image f  (Y ∪ Z) =
        inverse_image f Y ∪ inverse_image f Z := sorry

example {A B : Type} (f : A → B) (Y Z : Set B) :
    inverse_image f  (Y \ Z) =
        inverse_image f Y \ inverse_image f Z := sorry

example {A B : Type} (f : A → B) (Y Z : Set B) :
    Y ⊆ Z ↔ inverse_image f Y ⊆ inverse_image f Z := sorry

example {A B : Type} (f : A → B) (X : Set A) :
    inverse_image f (image f X) = X := sorry

example {A B : Type} (f : A → B) (Y : Set B) :
    image f (inverse_image f Y) = Y := sorry

example {A : Type} (f : A → A) (C : Set A) :
    closed f C → image f C ⊆ C := sorry

example {A : Type} (f : A → A) (C : Set A) :
    image f C ⊆ C → C ⊆ inverse_image f C := sorry

example {A : Type} (f : A → A) (C : Set A) :
    C ⊆ inverse_image f C → closed f C := sorry

example {A B : Type} (f : A → B) (g : B → A) (Y : Set B)
    (h1 : f ∘ g = id) (h2 : g ∘ f = id) :
    inverse_image f Y = image g Y := sorry