--------------------------------------------------------------------------------
--                                                                            --
-- Verified Datastructures and Algorithms for Satisfiability Testing          --
--                                                                            --
--------------------------------------------------------------------------------
--                                                                            --
-- This file contains the (strong) RAT specification.                         --
--                                                                            --
--------------------------------------------------------------------------------
--                                                                            --
-- Copyright (C) 2021-2023, Tobias Philipp                                    --
--                                                                            --
--------------------------------------------------------------------------------

pragma Ada_2022;
pragma Extensions_Allowed (On);

with SAT.Weak_Resolution;


package SAT.Strong_RAT is

      
   function Consequence (F : Formula_Type; C : Clause_Type) return Boolean
   is ((for all I of Interpretations =>
          (if Satisfies (I, F) then Satisfies (I, C))))
       with
         Ghost;
   
   pragma Annotate (GNATprove, Inline_For_Proof, Consequence);
   
   procedure Satisfies_Consequence
     (F : Formula_Type;
      C : Clause_Type;
      I : Interpretation_Type)
     with Pre => Consequence (F, C) and Satisfies (I, F),
     Post => Satisfies (I, C),
     Annotate => (GNATprove, Automatic_Instantiation),
     Ghost;
   
   procedure Equivalence_Consequence 
     (F : Formula_Type;
      C, D : Clause_Type)
     with Pre => Strong_RAT.Consequence (F, C) and then
     Equivalent (C, D),
     Post => Strong_RAT.Consequence (F, D),
     Annotate => (GNATprove, Automatic_Instantiation),
       Ghost;
   
   procedure Resolution_Appears
     (C, D : Clause_Type;
      L : Literal_Type)
     with Pre =>  C'Length + D'Length - 1 < 2 ** 16  and then
       Appears (C, L) and then
     Appears (D, Compl (L)) and then
     -- non tautological
     (for all Lp of C => not Appears (C, -Lp)) and then
     (for all Lp of D => not Appears (D, -Lp)) and then
       -- no doublicates
     Has_No_Duplicates (C) and then
     Has_No_Duplicates (D),
     Post => 
     not Appears (Weak_Resolution.Resolve (C, D, L), -L),
     Annotate => (GNATprove, Automatic_Instantiation),
     Ghost;

   function Spec (F : Formula_Type;
                  C : Clause_Type;
                  L : Literal_Type)
                  return Boolean
   is (Appears (C, L) and then
       (for all D of F => C'Length + D'Length < 2 ** 16) and then
       (for all D of F => (if Appears (D, -L) then Consequence (F, Weak_Resolution.Resolve (C, D, L)))))
     with Ghost;
   
   procedure Lemma_Interpretation
     (F : Formula_Type;
      C : Clause_Type;
      L : Literal_Type;
      I : Interpretation_Type)
     with 
       Pre => Spec (F, C, L) and Satisfies (I, F),
     Post => 
       (Satisfies (Guard (I, L), F) and then Satisfies (Guard (I, L), C)) or else
       (Satisfies (Guard (I, -L), F) and then Satisfies (Guard (I, -L), C)),
       Annotate => (GNATprove, Automatic_Instantiation),
       Ghost;
   
   procedure Lemma
     (F : Formula_Type;
      C : Clause_Type;
      L : Literal_Type)
     with Pre => Spec (F, C, L) and then Clause_Vector.Last (F) < Positive'Last,
     Post => Equisatisfiable (F, F.Add (C)),
       Ghost;
   

end SAT.Strong_RAT;
