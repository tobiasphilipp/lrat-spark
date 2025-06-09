--------------------------------------------------------------------------------
--                                                                            --
-- Verified Datastructures and Algorithms for Satisfiability Testing          --
--                                                                            --
--------------------------------------------------------------------------------
--                                                                            --
-- This file contains definitions and algorithms for verification of LRAT     --
-- proofs,                                                                    --
--                                                                            --
-- Restrictions:                                                              --
-- * Proof must be gapless.                                                   --
-- * Formula and proof must not contains tautologies.                         --
--                                                                            --
--------------------------------------------------------------------------------
--                                                                            --
-- Copyright (C) 2021-2023, Tobias Philipp                                    --
--                                                                            --
--------------------------------------------------------------------------------

pragma Unevaluated_Use_Of_Old (Allow);

with SPARK.Big_Integers;
with SAT.Strong_RAT;
with Literal_Vectors;

package SAT.LRAT 
with SPARK_Mode
is
   use type SPARK.Big_Integers.Big_Integer;
   
   -- Clause Storage

   type Clause_Pointer_Type is access Clause_Type;
   
   type Entry_Type 
   is record
      Deleted : Boolean;
      Clause : Clause_Pointer_Type;
   end record;
   
   Null_Entry_Type : constant Entry_Type := 
     Entry_Type'(Deleted => False, Clause => null);
   
   subtype Extended_Index_Type is Natural;
   
   subtype Index_Type is Extended_Index_Type
   range Extended_Index_Type'First + 1 .. Extended_Index_Type'Last;
   
   type Container_Type is array (Index_Type range 1 .. <>) of Entry_Type;	
   
   type Container_Access_Type is access Container_Type;
   
   Container     : Container_Access_Type;
   Next_Id       : Extended_Index_Type;
   
   Max_Clause_Id : Extended_Index_Type;
   Num_Vars      : Natural;
   
   type Integer_Array is array (Integer range <>) of Integer;
   type Integer_Array_Ptr is access Integer_Array;
   
   False_Assignment : Integer_Array_Ptr;
   Repair_Vec : Literal_Vectors.Vector;
   
   -- Correspondance of False_Assignment and (ghost) assignment.
   function FA_Assignment_Correspondance
     (FA : Integer_Array_Ptr; A : Assignment_Type) return Boolean
   is (
       FA /= null and then
       (for all I in FA'Range => (if I in Literal_Type and then FA (I) = 1 then
                                     Appears (A, Literal_Type (-I)))) and then
       (for all L of A => -L in FA'Range and then FA (-L) = 1))
       with Ghost;
   
   Empty_Clause_Inserted : Boolean;
   
   -- Ghost model of the formula
   Working_Formula : Formula_Type with Ghost;
   Input_Formula : Formula_Type with Ghost;
   
   -- Maps Indices to indices of working formula
   type Map_WFC_Type is array (Positive range Positive'First .. Positive'Last) of Extended_Index_Type;
   type Map_CWF_Type is array (Index_Type range Index_Type'First .. Index_Type'Last) of Natural;
   
   Map_WFC : Map_WFC_Type := (others => 0) with Ghost;
   Map_CWF : Map_CWF_Type := (others => 0) with Ghost;
   
   -- Correspondance of working formula and clause storage
   function Correspondance return Boolean is
     (Container'First = 1 and then
      Container'Last = Max_Clause_Id and then 
      Max_Clause_Id > 0 and then
      Next_Id <= Max_Clause_Id  and then 
      Working_Formula.Length <= SPARK.Big_Integers.To_Big_Integer (Integer (Next_Id)) and then
      
        (for all I of Map_WFC => I < Next_Id) and then
      
          (for all I of Map_CWF => I <= Working_Formula.Last) and then
      
          (for all I in Map_CWF'Range =>
               (for all J in Map_CWF'Range =>
                  (if I /= J and then Map_CWF (I) /= 0 then Map_CWF (I) /= Map_CWF (J)))) and then
      
          (for all I in Map_WFC'Range =>
               (for all J in Map_WFC'Range =>
                  (if I /= J and then Map_WFC (I) /= 0 then Map_WFC (I) /= Map_WFC (J)))) and then
      
          (for all I in Map_WFC'Range =>
               (if Map_WFC (I) /= 0 then 
                       Container (Map_WFC (I)).Clause /= null and then 
                Map_CWF (Map_WFC (I)) = I)) and then
      
        (for all I in 1 .. Clause_Vector.Last (Working_Formula) =>
              Map_WFC (I) in Index_Type and then
         Container (Map_WFC (I)).Clause /= null and then
         Clause_Vector.Get (Container => Working_Formula,
                            Position => I)
         =
           Container (Map_WFC (I)).Clause.all) and then
      
          (for all I in 1 .. Next_Id - 1 =>
               (if Container (I).Clause /= null then 
                       Map_CWF (I) <= Clause_Vector.Last (Working_Formula) and then
                Map_CWF (I) > 0 and then 
                Clause_Vector.Get (Container => Working_Formula,
                                   Position => Map_CWF (I))
                =
                  Container (I).Clause.all)) and then 
      
        (for all I in Next_Id .. Container'Last =>
              Container (I).Clause = null and Map_CWF (I) = 0) and then
      
          (Extended_Index_Type (Clause_Vector.Last (Working_Formula)) <= Container'Last)
     )
       with Ghost,
     Pre => Container /= null;  
               
   -- Preserved invariants
   function Invariant return Boolean
   is (Container /= null and then
       False_Assignment /= null and then
       False_Assignment'First = -Num_Vars and then
       False_Assignment'Last = Num_Vars and then
       Correspondance and then
       
       -- all literals in the formula are in the range
         (for all I in Container'Range => (if Container (I).Clause /= null then
                                             (for all L of Container (I).Clause.all =>
                                                   L in -Num_Vars .. Num_Vars)))
         
      )
     with Ghost;
                                       
   -- Operations
   
   type Operation_Result_Type is 
     (Successful, -- designates a succesful operation
      Failure,    -- failure means that an operation was unsuccesful, 
                  -- but operations can continue
      Crash       -- a crash designates that we cannot recover
     );
   
   use type Formula_Type;
   
   -- The initialization procedure creates a container for holding all clauses.
   -- The clauses are represented by the ghost model Working_Formula.
   -- As memory is allocated, the operation may designate a crash
   procedure Init
     (Number_Clauses   : in     Extended_Index_Type;
      Number_Variables : in     Natural;
      Result           :    out Operation_Result_Type)
     with Post =>
       (case Result is
          when Successful => Invariant and Working_Formula = Empty_Formula,
          when Failure    => False,
          when Crash      => True);
   
   -- The insertion procedure inserts a clause with the preferred Id.
   -- Ids must be given ordered.
   procedure Insert_Clause
     (C      : in     Clause_Type;
      Id     : in     Extended_Index_Type;
      Result :    out Operation_Result_Type)
     with
     Pre => 
       Invariant and then 
         (for all L of C => L in -Num_Vars .. Num_Vars),
     Post =>
       (case Result is 
          when Successful => 
            Invariant and then
              Working_Formula = Working_Formula'Old.Add (C),
          when Failure    =>
            Invariant and then 
              Working_Formula = Working_Formula'Old,
          when Crash      => 
            True);
   
   type Hint_Type is array (Natural range 0 .. <>) of Integer
     with
     Dynamic_Predicate =>
         Hint_Type'Last < 2**16;
   
   -- This procedure checks whether a given clause has the Reverse Unit 
   -- Propagation (RUP) property. It guarantees that the working formula
   -- entails the clause.
   procedure Check_RUP_Clause
     (C      : in     Clause_Type;
      Hints  : in     Hint_Type;
      Result :    out Operation_Result_Type)
     with Pre => Invariant and then Next_Id < Container'Last,
     Post =>
       (case Result is 
          when Successful => 
            Invariant and then 
              Strong_RAT.Consequence (Working_Formula, C) and then 
              Unsat_Preservation (Working_Formula, Working_Formula.Add (C)),
          when Failure => Invariant,
          when Crash   => True
       );
   
   -- The deletion procedure deletes a clause with the given Id.
   -- Note that the post-condition does not guarantee deletion of the par
   procedure Delete_Clause
     (Id     : in     Index_Type;
      Result :    out Operation_Result_Type)
   with
     Pre => Invariant and then Id >= 1,
     Post =>
       (case Result is 
          when Successful => 
            Invariant and then 
              Unsat_Preservation (Working_Formula'Old, Working_Formula),
          when Failure => Invariant,
          when Crash   => False
       );
   
   procedure Check_RAT_Clause
     (C      : in     Clause_Type;
      Hints  : in     Hint_Type;
      Result :    out Operation_Result_Type)
   with
     Pre => Invariant and then Next_Id < Container'Last and then C'Length > 0,
     Post =>
       (case Result is 
          when Successful => 
            Invariant and then 
              Unsat_Preservation (Working_Formula, Working_Formula.Add (C)),
          when Failure => Invariant,
          when Crash   => False
       );
   
   procedure Increase_Num_Vars
     (New_Num_Vars : Natural;
      Result : out Operation_Result_Type)
     with Pre => (Invariant and New_Num_Vars > Num_Vars),
     Post => (if Result = Successful then Invariant and Num_Vars = New_Num_Vars);
   
   procedure Increase_Container
     (Minimum : in     Natural;
      Result  :    out Operation_Result_Type)
     with
       Pre => Invariant,
       Post => 
       (case Result is 
          when Successful => 
            Invariant and then
              Next_Id < Container'Last and then 
              Working_Formula = Working_Formula'Old and then
              Minimum <= Container'Last,
          when Failure    =>
            Invariant and then 
              Working_Formula = Working_Formula'Old,
          when Crash      => 
            True);
   
   procedure Parse_Formula
     (Filename : in     String;
      Result   :    out Operation_Result_Type)
     with Post => (if Result = Successful then Invariant and Input_Formula = Working_Formula);
   
   procedure Check_Proof
     (Filename : in     String;
      Result   :    out Operation_Result_Type)
     with Pre => (Invariant and Input_Formula = Working_Formula),
     Post => (if Result = Successful then not Satisfiable (Input_Formula));
   
   procedure Check
     (Formula_Filename : in     String;
      Proof_Filename   : in     String;
      Result           :    out Operation_Result_Type)
     with Post => (if Result = Successful then not Satisfiable (Input_Formula));

end SAT.LRAT;
