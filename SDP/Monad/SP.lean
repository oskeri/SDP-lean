import Mathlib.Data.List.Basic

/-!
# The simple probability (SP) monad

A monad associating each entry with a probability.

## Implementation notes

The probability is represented as a "weight" (natural number). The corresponding
probability of an entry with weight `w` can be defined as `w` divided by the sum of all weights.

-/

/-- The SP monad. -/

inductive SP (A : Type) : Type
  | mkSP : List (Nat × A) → SP A

namespace SP

/-- Retrieve the underlying list of weights and elements. -/

def toList : SP A → List (Nat × A)
  | mkSP l => l

/-- The empty SP monad. -/

def nil : SP A := mkSP []

/-- Extending an SP monad with a new entry. -/

def cons (x : Nat × A) : SP A → SP A
  | mkSP l => mkSP (x :: l)

/-- Evaluation law for `toList`. -/

@[simp] theorem toList_eq : (l : SP A) → toList l = l.1 := by
  simp [toList]

/-- Evaluation law for `nil`. -/

@[simp] theorem nil_eq_nil : @nil A = mkSP [] := by
  simp [nil]

/-- Evaluation law for `cons`. -/

@[simp] theorem cons_eq_cons (x : Nat × A) (l : List (Nat × A)) : cons x (mkSP l) = mkSP (x :: l) := by
  simp [cons]

/-- Evaluation law for `cons`. -/

@[simp] theorem cons_eq_cons' (x : Nat × A) (l : SP A) : cons x l = mkSP (x :: l.toList) := by
  simp [cons]

/-- Applying a function to an entry without changing its weight. -/

def ap (f : A → B) : Nat × A → Nat × B
  | (w, a) => (w, f a)

/-- An evaluation law for `ap`. -/

@[simp] theorem ap_fst (f : A → B) (x : Nat × A) : (ap f x).1 = x.1 := rfl

/-- An evaluation law for `ap`. -/

@[simp] theorem ap_snd (f : A → B) (x : Nat × A) : (ap f x).2 = f x.2 := rfl

/-- A `map` function for the `SP` monad. -/

def map (f : A → B) : SP A → SP B
  | mkSP l => mkSP (List.map (ap f) l)

/-- The sum of the weights of all entries -/

def totalWeight : SP A → Nat
  | mkSP l => List.sum (List.map (fun x => x.1) l)

/-- The total weight of `nil` is `0` -/

@[simp] theorem totalWeight_nil : @totalWeight A nil = 0 := by
  simp [totalWeight]

/-- The total weight of `cons x l` is the weight of `x` plus the total weight of `l`. -/

@[simp] theorem totalWeight_cons : totalWeight (cons x l) = x.1 + totalWeight l := by
  simp [totalWeight]

/-- Scale all weights by some amount. -/

def scaleWeights (w : Nat) : SP A → SP A
  | mkSP l => mkSP (List.map (fun (w',x) => (w * w', x)) l)

/-- Scaling the weights of `nil` is equal to `nil`. -/

@[simp] theorem scaleWeights_nil : @scaleWeights A w nil = nil := by
  simp [scaleWeights]

/-- Scaling the weights of `cons x l` is equal to scaling `x` and scaling `l`. -/

@[simp] theorem scaleWeights_cons (w : Nat) (x : Nat × A) (sp : SP A) :
  scaleWeights w (cons x sp) = cons (w * x.1, x.2) (scaleWeights w sp) := by
  simp [scaleWeights]

/-- Remove impossible entries (with weight `0`). -/

def dropImpossible : SP A → SP A
  | mkSP l => mkSP (List.filter (fun (w,_) => w ≠ 0) l)

/-- An `Append` instance for `SP`. -/

instance : Append (SP A) where
  append xs ys := mkSP (xs.toList ++ ys.toList)

/-- `nil` is a right identity for append. -/

@[simp] theorem append_nil (as : SP α) : as ++ nil = as := by
  simp [HAppend.hAppend]
  simp [Append.append, instAppend]

/-- `nil` is a left identity for append. -/

@[simp] theorem nil_append (as : SP α) : nil ++ as = as := rfl

/-- Appending `cons b bs` from the right. -/

@[simp] theorem append_cons (b : Nat × α) (as bs : SP α) : as ++ (cons b bs) = as ++ cons b nil ++ bs := by
  simp [HAppend.hAppend]
  simp [Append.append, instAppend]

/-- Appending `cons b bs` from the left. -/

@[simp] theorem cons_append (a : Nat × α) (as bs : SP α) : (cons a as) ++ bs = cons a (as ++ bs) := rfl

/-- Appending a singleton from the left. -/

@[simp] theorem singleton_append (a : Nat × α) (as : SP α) : cons a nil ++ as = cons a as := by
  rw [cons_append, nil_append]

/-- Flatten / join for the monad. -/

def flatten : (SP (SP A)) -> SP A
  | mkSP l => List.foldr (fun (w, xs) ys => scaleWeights w xs ++ ys) nil l

/-- Flattening `nil` is equal to `nil`. -/

@[simp] theorem flatten_nil : @flatten A nil = nil := by
  rfl

/-- Flattening `cons`. -/

@[simp] theorem flatten_cons :
  flatten (.cons x xs) = scaleWeights x.1 x.2 ++ flatten xs := by
  simp [flatten]

/-- A `Monad` instance for `SP`. -/

instance : Monad SP where
  pure x := cons (1,x) nil
  bind x f := flatten (mkSP (List.map (ap f) x.toList))
  map := map

/-- The map of the monad is equal to `map`. -/

@[simp] theorem map_eq_map {f : A → B} {l : SP A} :
  f <$> l = map f l := by rfl

/-- The map of the monad is equal to `List.map`. -/

theorem map_eq_ap_map {f : A → B} {l : SP A} :
  f <$> l = mkSP (List.map (ap f) l.toList) := by rfl

/-- The total weight is preserved by `map`. -/

@[simp] theorem totalWeight_map {f : A → B} {l : SP A} :
  totalWeight (map f l) = totalWeight l := by
  match l with
  | mkSP l =>
  simp [map, totalWeight]
  induction l
  · case nil => rfl
  · case cons h t IH =>
    have (_,_) := h
    simp [IH]

/-- A `toString` instance for `SP`. -/

instance instToStringSP [ToString α] : ToString (SP α) where
  toString
    | mkSP l =>
      String.intercalate "\n"
        (List.map (go (totalWeight (mkSP l)))
          (List.mergeSort l (fun (w,_) (w',_) => w' ≤ w)))
  where
  go (wTot : Nat) : Nat × α → String
    | (w , a) =>
      toString a ++ " (" ++ toString w ++ "/" ++ toString wTot ++ ")"
