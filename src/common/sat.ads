--------------------------------------------------------------------------------
--                                                                            --
-- Verified Datastructures and Algorithms for Satisfiability Testing          --
--                                                                            --
--------------------------------------------------------------------------------
--                                                                            --
-- This file contains basic definitions such as literals, clauses, formulas   --
-- and interpretations.                                                       --
--                                                                            --
--------------------------------------------------------------------------------
--                                                                            --
-- Copyright (C) 2021-2023, Tobias Philipp                                    --
--                                                                            --
--------------------------------------------------------------------------------

pragma Ada_2022;
pragma Extensions_Allowed (On);

with SPARK.Containers.Functional.Vectors;

package SAT with
SPARK_Mode => On,
  Always_Terminates
is
   --------------
   -- Literals --
   --------------

   subtype Literal_Type is Integer with
       Static_Predicate =>
        Literal_Type /= 0 and then Literal_Type > -2**31 + 1
        and then Literal_Type < 2**31 - 1;

   function Compl (Literal : Literal_Type) return Literal_Type is
     (-Literal) with
     Pre =>
      Literal /= 0 and then Literal > Integer'First
      and then Literal < Integer'Last,
     Post =>
      Compl'Result /= 0 and then Compl'Result > Integer'First
      and then Compl'Result < Integer'Last;

   -------------
   -- Clauses --
   -------------

   type Clause_Type is array (Natural range 0 .. <>) of Literal_Type with
     Dynamic_Predicate =>
      Clause_Type'First = 0 and then Clause_Type'Last < 2**16;

   Empty_Clause : constant Clause_Type := []; 

   function Appears (C : Clause_Type; L : Literal_Type) return Boolean is
     (for some Lp of C => L = Lp) with
     Post => Appears'Result = (for some Lp of C => L = Lp);
   
   function Subset
     (C, D : Clause_Type) return Boolean
   is (for all L of C => Appears (D, L));
   
   function Equivalent
     (C, D : Clause_Type) return Boolean
   is ((for all L of C => Appears (D, L)) and
       (for all L of D => Appears (C, L)))	
  with	    
    Global => null;	
       

   function Has_No_Duplicates
     (C : Clause_Type)
     return Boolean
   is
      (for all I in C'First .. C'Last =>
	 (for all J in C'First .. C'Last =>
	    (if I /= J then C (I) /= C (J))));

   -- In many contexts, duplicate literals in the area of SAT solvers are
   -- annoying; thus we like to eliminate them
   function Remove_Duplicate_Literals
     (C : in Clause_Type) return Clause_Type
   with Post =>
     -- The set representation is equal
     Equivalent (C, Remove_Duplicate_Literals'Result) and then
     -- no duplicate entries
     Has_No_Duplicates (Remove_Duplicate_Literals'Result) and then
     -- size can decrease, not increase
     Remove_Duplicate_Literals'Result'Length <= C'Length;
   
   function Tautology (C : Clause_Type) return Boolean
     is (for some L of C => Appears (C, -L));
   

   -------------
   -- Formulas --
   -------------

   package Clause_Vector is new SPARK.Containers.Functional.Vectors
     (Index_Type => Positive, Element_Type => Clause_Type);

   subtype Formula_Type is Clause_Vector.Sequence;

   function Contains (F : Formula_Type; C : Clause_Type) return Boolean is
     (for some I in Positive'First .. Clause_Vector.Last (F) =>
           Clause_Vector.Get (F, I) = C);
   
   -- F is a subset of G, where clauses may be reordered
   function Subset (F, G : Formula_Type) return Boolean 
   is (for all C of F => (for some D of G => Equivalent (C, D)));
   
   -- F contains the same clauses as G, but clauses may be reordered
   function Equivalent (F, G : Formula_Type) return Boolean
   is (Subset (F, G) and Subset (G, F));
   
   Empty_Formula : constant Formula_Type := Clause_Vector.Empty_Sequence;

   ---------------------
   -- Interpretations --
   ---------------------
   
   

   type Interpretation_Type is array (Natural range 0 .. 2**31 - 1) of Boolean; --) o 2**31 - 1) of Boolean;
   type Interpretation_Cursor_Type  is
      record
         Overflow : Boolean;
               I : Interpretation_Type;
      end record;   

   type All_Interpretations is private with
     Iterable =>
       (First       => First_Interpretation,
        Next        => Next_Interpretation,
        Has_Element => Interpretation_Has_Element,
        Element     => Interpretation_Element,
        Last        => Last_Interpretation);

   pragma Warnings (Off, "unused variable");

   function First_Interpretation
     (K : All_Interpretations) return Interpretation_Cursor_Type is
     (Interpretation_Cursor_Type'(Overflow=>False, I => (others => False)));
   
   function Last_Interpretation
     (K : All_Interpretations) return Interpretation_Cursor_Type is
     (Interpretation_Cursor_Type'(Overflow=>False, I => (others => True)));
   
   function Interpretation_Has_Element
     (K : in All_Interpretations; J : Interpretation_Cursor_Type) return Boolean is
     (not J.Overflow); 

   function Next_Interpretation
     (K : All_Interpretations; I : in Interpretation_Cursor_Type)
      return Interpretation_Cursor_Type with
     Pre => not I.Overflow;

   function Interpretation_Element
     (K : in All_Interpretations; I : in Interpretation_Cursor_Type)
      return Interpretation_Type is
     (I.I) with
     Pre => not I.Overflow;

   pragma Warnings (On, "unused variable");

   function Interpretations return All_Interpretations;
   
   function Guard (I : Interpretation_Type; L : Literal_Type)
                   return Interpretation_Type
   is (if L > 0 then (I with delta L => True) else (I with delta -L => False))
     with Post => Guard'Result = (if L > 0 then (I with delta L => True) else (I with delta -L => False));
   pragma Annotate (GNATprove, Inline_For_Proof, Guard);
     
   function Get_Model (F : Formula_Type) return Interpretation_Type
     with Pre => Satisfiable (F),
     Post => Satisfies (Get_Model'Result, F),
     Ghost,
     Import;


   
   ----------------
   -- Assignment --
   ----------------
   
   package Assignment_Vector is new SPARK.Containers.Functional.Vectors
     (Index_Type   => Positive,
      Element_Type => Literal_Type);

   use type Assignment_Vector.Sequence;

   subtype Assignment_Type is Assignment_Vector.Sequence;

   -- A literal appears in an assignment
   function Appears
     (A : Assignment_Type;
      L : Literal_Type) return Boolean
   is (for some Lp of A => L = Lp);

   -- A literal L appears in the assignment and thus is true under A
   function Is_True
     (A : Assignment_Type;
      L : Literal_Type) return Boolean
   is (Appears (A, L));

   -- The complement of L appears in an assignment and thus is false under A
   function Is_False
     (A : Assignment_Type;
      L : Literal_Type) return Boolean
   is (Appears (A, Compl (L)));

   ---------------------------
   -- Satisfaction Relation --
   ---------------------------

   function Satisfies
     (I : Interpretation_Type; L : Literal_Type) return Boolean is
     (if L > 0 then I (L) else not I (-L));

   function Satisfies
     (I : Interpretation_Type; C : Clause_Type) return Boolean is
     (for some L of C => Satisfies (I, L));

   function Satisfies
     (I : Interpretation_Type; F : Formula_Type) return Boolean is
     (for all C of F => Satisfies (I, C));
   
   function Satisfies
     (I : Interpretation_Type; A : Assignment_Type) return Boolean
   is (for all L of A => Satisfies (I, L));
   
   -- Clause and Formula Ordering is irrelevant
   
   procedure Satisfies_Clause_Ordering_Irrelevant
     (I : Interpretation_Type;
      C : Clause_Type;
      D : Clause_Type)
     with Pre => Equivalent (C, D),
     Post => Satisfies (I, C) = Satisfies (I, D),
     Annotate => (GNATprove, Automatic_Instantiation),
     Ghost;
   
   procedure Satisfies_Formula_Ordering_Irrelevant
     (I : Interpretation_Type;
      F : Formula_Type;
      G : Formula_Type)
     with Pre => Equivalent (F, G),
     Post => Satisfies (I, F) = Satisfies (I, G),
     Annotate => (GNATprove, Automatic_Instantiation),
     Ghost;
   
   procedure Clause_Satisfaction_Binary
     (I : Interpretation_Type;
      A, B : Literal_Type)
     with 
       Ghost,
         Annotate => (GNATprove, Automatic_Instantiation),
       Post => (Satisfies (I, [A, B]) = (Satisfies (I, A) or Satisfies (I, B)));
   
    procedure Clause_Satisfaction_Ternary
     (I : Interpretation_Type;
      A, B, C : Literal_Type)
     with 
       Ghost,
         Annotate => (GNATprove, Automatic_Instantiation),
       Post => (Satisfies (I, [A, B, C]) = Satisfies (I, A) or Satisfies (I, B) or Satisfies (I, C));
        
     
   procedure Completeness
     (I : Interpretation_Type)
     with
       Post => (for some J of Interpretations => (for all L in Interpretation_Type'Range => I (L) = J (L))),
       Annotate => (GNATprove, Automatic_Instantiation),
       Ghost;
   
   --------------------
   -- Satisfiability --
   --------------------

   function Satisfiable (F : Formula_Type) return Boolean is
     (for some J in Interpretations => Satisfies (Interpretation_Element (Interpretations, J), F)) with
     Post => Satisfiable'Result = (for some J of Interpretations => Satisfies (J, F)),
     Ghost;
   pragma Annotate (GNATprove, Inline_For_Proof, Satisfiable);
   
   procedure Satisfiable_Subset
     (F, G : Formula_Type)
     with
       Ghost,
       Pre => Subset (F, G),
       Annotate => (GNATprove, Automatic_Instantiation),
       Post => (if Satisfiable (G) then Satisfiable (F)) and (if not Satisfiable (F) then not Satisfiable (G));
   
   procedure Satisfaction_Implies_Satisfiability
     (F : Formula_Type;
      I : Interpretation_Type)
     with Pre => Satisfies (I, F),
     Post => Satisfiable (F),
       Annotate => (GNATprove, Automatic_Instantiation),
       Ghost;

      
   function Unsat_Preservation (F, G : Formula_Type) return Boolean is
     (if not Satisfiable (G) then not Satisfiable (F))
       with Post => Unsat_Preservation'Result = (if not Satisfiable (G) then not Satisfiable (F)),
       Ghost;
   pragma Annotate (GNATprove, Inline_For_Proof, Unsat_Preservation);
   
   ------------------
   -- Consequence  --
   ------------------
   function Consequence (F, G : Formula_Type) return Boolean is
     (for all I in Interpretations =>
        (if Satisfies (Interpretation_Element (Interpretations, I), F) then Satisfies (Interpretation_Element (Interpretations, I), G))) with
       Ghost;
   
   -------------------------
   -- Logical Equivalence --
   -------------------------
   function Equivalence (F, G : Formula_Type) return Boolean is
     (Consequence (F, G) and then Consequence (G, F))
       with Ghost;
   
   ------------------------
   -- Equisatisfiability --
   ------------------------
   function Equisatisfiable (F, G : Formula_Type) return Boolean
   is ((if Satisfiable (F) then Satisfiable (G)) and then
         (if Satisfiable (G) then Satisfiable (F)))
       with Ghost;
   
   procedure Equivalence_Implies_Equisatisfiability
     (F, G : Formula_Type)
     with Pre => Equivalence (F, G),
     Post => Equisatisfiable (F, G),
     Global => null,
     Annotate => (GNATprove, Automatic_Instantiation),
     Ghost;


   pragma Warnings (Off, "has no effect");

   procedure Empty_Clause_Lemma (F : Formula_Type) with
     Pre => (for some C of F => C'Length = 0), Post => not Satisfiable (F);

   pragma Warnings (On, "has no effect");

private

   type All_Interpretations is null record;

end SAT;
