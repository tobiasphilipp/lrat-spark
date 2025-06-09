--------------------------------------------------------------------------------
--                                                                            --
-- Verified Datastructures and Algorithms for Satisfiability Testing          --
--                                                                            --
--------------------------------------------------------------------------------
--                                                                            --
-- This file contains the weak resolution rule and corresponding lemmas.      --
--                                                                            --
-- Weakly resolving two clauses C and D upon the literal L is defined as      --
-- follows:                                                                   --
-- 1. L appears in C,                                                         --
-- 2. -L appears in D,                                                        --
-- 3. the resolvent is C \/ (D without -L)                                    --
--                                                                            --
--------------------------------------------------------------------------------
--                                                                            --
-- Copyright (C) 2021-2023, Tobias Philipp                                    --
--                                                                            --
--------------------------------------------------------------------------------

pragma Overflow_Mode (General => Strict, Assertions => Eliminated);

package SAT.Weak_Resolution 
  with SPARK_Mode
is
   function Specification
     (C : Clause_Type;
      D : Clause_Type;
      L : Literal_Type;
      R : Clause_Type)
   return Boolean
   is
     (
        (for all Lit of C => Appears (R, Lit)) and then 
          (for all Lit of D => (if Lit /= -L then Appears (R, Lit))) and then
          (for all Lit of R => (if Lit = -L then Appears (C, Lit) else (Appears (C, Lit) or else Appears (D, Lit)))) and then
      Has_No_Duplicates (R)
     );
   
   procedure Lemma_Interpretation
     (F : in Formula_Type;
      C : in Clause_Type;
      D : in Clause_Type;
      L : in Literal_Type;
      R : in Clause_Type;
      I : in Interpretation_Type)
   with
     Pre =>
       Clause_Vector.Last (F) < Positive'Last and then
         Contains (F, C) and then
         Contains (F, D) and then
         Appears (C, L) and then
         Appears (D, -L) and then
         Specification (C, D, L, R) and then
         Satisfies (I, F),
         Post => Satisfies (I, Clause_Vector.Add (F, R)),
         Annotate => (GNATprove, Automatic_Instantiation),
     Ghost;
   
   function Resolve
     (C : Clause_Type;
      D : Clause_Type;
      L : Literal_Type)
      return Clause_Type
     with
       Pre  =>
         C'Length + D'Length - 1 < 2 ** 16 and then 
       Appears (C, L) and then
         Appears (D, Compl (L)),
         --Has_No_Duplicates (C) and then
         --Has_No_Duplicates (D),
         
     Post =>
       Specification (C, D, L, Resolve'Result),
       Global => null;

   procedure Workaround_Resolve_Equality
     (C, D, E : Clause_Type;
      Pivot : Literal_Type)
     with 
       Pre => D = E and then 
       D'First = E'First and then
       D'Last = E'Last and then
       (for all I in D'Range => D (I) = E (I)) and then 
       C'Length + D'Length - 1 < 2 ** 16 and then 
       Appears (C, Pivot) and then
       Appears (D, Compl (Pivot)),
       Post => Equivalent (Resolve (C, D, Pivot),
                           Resolve (C, E, Pivot)),
       Annotate => (GNATprove, Automatic_Instantiation),
         Ghost;

   procedure Lemma
     (F : in Formula_Type;
      C : in Clause_Type;
      D : in Clause_Type;
      L : in Literal_Type;
      R : in Clause_Type) 
   with
     Pre =>
       Clause_Vector.Last (F) < Positive'Last and then
         Contains (F, C) and then
         Contains (F, D) and then
         Appears (C, L) and then
         Appears (D, -L) and then
         Specification (C, D, L, R),
     Post => Consequence (F, Clause_Vector.Add (F, R)),
     Ghost;

end SAT.Weak_Resolution;
