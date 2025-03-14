-- The simple probability monad

-- Probabilities are represented as "weights" (natural numbers)
-- The corresponding probability of an entry with weight w is given by
-- w divided by the sum of all weights.

import Mathlib.Data.List.Basic

inductive SP (A : Type) : Type
  | mkSP : List (Nat × A) → SP A

namespace SP

def toList : SP A → List (Nat × A)
  | mkSP l => l

def nil : SP A := mkSP []
def cons (x : Nat × A) : SP A → SP A
  | mkSP l => mkSP (x :: l)

@[simp] theorem toList_eq : (l : SP A) → toList l = l.1 := by
  simp [toList]

@[simp] theorem nil_eq_nil : @nil A = mkSP [] := by
  simp [nil]

@[simp] theorem cons_eq_cons (x : Nat × A) (l : List (Nat × A)) : cons x (mkSP l) = mkSP (x :: l) := by
  simp [cons]

@[simp] theorem cons_eq_cons' (x : Nat × A) (l : SP A) : cons x l = mkSP (x :: l.toList) := by
  simp [cons]

def ap (f : A → B) : Nat × A → Nat × B
  | (w, a) => (w, f a)

@[simp] theorem ap_fst (f : A → B) (x : Nat × A) : (ap f x).1 = x.1 := rfl

@[simp] theorem ap_snd (f : A → B) (x : Nat × A) : (ap f x).2 = f x.2 := rfl

def map (f : A → B) : SP A → SP B
  | mkSP l => mkSP (List.map (ap f) l)

-- The sum of the weights

def totalWeight : SP A → Nat
  | mkSP l => List.sum (List.map (fun x => x.1) l)

@[simp] theorem totalWeight_nil : @totalWeight A nil = 0 := by
  simp [totalWeight]

@[simp] theorem totalWeight_cons : totalWeight (cons x l) = x.1 + totalWeight l := by
  simp [totalWeight]


def scaleWeights (w : Nat) : SP A → SP A
  | mkSP l => mkSP (List.map (fun (w',x) => (w * w', x)) l)

@[simp] theorem scaleWeights_nil : @scaleWeights A w nil = nil := by
  simp [scaleWeights]

@[simp] theorem scaleWeights_cons (w : Nat) (x : Nat × A) (sp : SP A) :
  scaleWeights w (cons x sp) = cons (w * x.1, x.2) (scaleWeights w sp) := by
  simp [scaleWeights]

-- @[simp] theorem scaleWeights_one (sp : SP A) : scaleWeights 1 sp = sp := by
--   match sp with
--   | mkSP l =>
--   induction l
--   · rw [scaleWeights, nil]
--   · case cons h t IH =>
--     simp [scaleWeights,IH]

instance : Append (SP A) where
  append xs ys := mkSP (xs.toList ++ ys.toList)

@[simp] theorem append_nil (as : SP α) : as ++ nil = as := by
  simp [HAppend.hAppend]
  simp [Append.append, instAppend]

@[simp] theorem nil_append (as : SP α) : nil ++ as = as := rfl

@[simp] theorem append_cons (b : Nat × α) (as bs : SP α) : as ++ (cons b bs) = as ++ cons b nil ++ bs := by
  simp [HAppend.hAppend]
  simp [Append.append, instAppend]

@[simp] theorem cons_append (a : Nat × α) (as bs : SP α) : (cons a as) ++ bs = cons a (as ++ bs) := rfl

@[simp] theorem singleton_append (a : Nat × α) (as : SP α) : cons a nil ++ as = cons a as := by
  rw [cons_append, nil_append]

def flatten : (SP (SP A)) -> SP A
  | mkSP l => List.foldr (fun (w, xs) ys => scaleWeights w xs ++ ys) nil l

@[simp] theorem flatten_nil : @flatten A nil = nil := by
  rfl

@[simp] theorem flatten_cons :
  flatten (.cons x xs) = scaleWeights x.1 x.2 ++ flatten xs := by
  simp [flatten]

instance : Monad SP where
  pure x := cons (1,x) nil
  bind x f := flatten (mkSP (List.map (ap f) x.toList))
  map := map

@[simp] theorem map_eq_map {f : A → B} {l : SP A} :
  f <$> l = map f l := by rfl

theorem map_eq_ap_map {f : A → B} {l : SP A} :
  f <$> l = mkSP (List.map (ap f) l.toList) := by rfl

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



-- @[simp] theorem map_totalWeight' {f : A → B} {l : SP A} :
--   totalWeight (f <$> l) = totalWeight l := by
--   simp [Functor.map]
--   admit
