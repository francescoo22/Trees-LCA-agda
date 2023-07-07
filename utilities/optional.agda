module utilities.optional where
  data Optional (A : Set) : Set where
    none : Optional A
    some : A → Optional A
