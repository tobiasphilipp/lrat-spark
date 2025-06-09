with Ada.Text_IO;
with Ada.Unchecked_Deallocation;
with Ada.Exceptions;


with SAT.Unit_Reduct;
with SAT.Weak_Resolution;
with SAT.Strong_RAT;
with SAT.Parsing;


with Integer_Vectors;

with SPARK.Alloc;
with SPARK.Cut_Operations; use SPARK.Cut_Operations;

with Trace;

package body SAT.LRAT
  with SPARK_Mode
is
   
   procedure Free_Assignment is new Ada.Unchecked_Deallocation	
     (Object => Integer_Array, Name => Integer_Array_Ptr);	
   
   procedure Free_Container is new Ada.Unchecked_Deallocation	
     (Object => Container_Type, Name => Container_Access_Type);	
   
   -- --------------------------------------------------------------------------
   
   procedure Init
     (Number_Clauses : in Extended_Index_Type;
      Number_Variables : in Natural;
      Result : out Operation_Result_Type)
   is
      
   begin
      Container := new Container_Type'([for I in 1 .. Number_Clauses => Entry_Type'(Deleted => False, Clause => null)]);
      pragma Annotate (GNATprove, False_Positive, "resource or memory leak might occur", "Intentional");
      
      False_Assignment := new Integer_Array'([for I in -Number_Variables .. Number_Variables => 0]);
      pragma Annotate (GNATprove, False_Positive, "resource or memory leak might occur", "Intentional");
      
      if
        Container /= null and
        False_Assignment /= null and
        Number_Clauses > 0
      then
         Next_Id := Container'First;
         Working_Formula := Empty_Formula;
         Max_Clause_Id := Number_Clauses;
         Num_Vars := Number_Variables;
         
         
         Map_WFC := (others => 0);
         Map_CWF := (others => 0);
         
         pragma Assert (Correspondance);
         
         Result := Successful;
      else
         Result := Crash;
      end if;
   end Init;
   
   -- --------------------------------------------------------------------------
   
   procedure Insert_Clause
     (C      : in Clause_Type;
      Id     : in Extended_Index_Type;
      Result : out Operation_Result_Type)
   is
      Old_Working_Formula : constant Formula_Type := Working_Formula with Ghost;

   begin      
      if Id < Next_Id then
         Ada.Text_IO.Put_Line ("ERROR: existing clause ID cannot be overwritten.");
         Ada.Text_IO.Put ("requested id = ");
         Ada.Text_IO.Put (Id'Image);
         Ada.Text_IO.Put ("minimal id = ");
         Ada.Text_IO.Put_Line (Next_Id'Image);
         
         Result := Failure;
         return;
      end if;
      
      if Next_Id not in Container'Range or else Next_Id >= Max_Clause_Id or else Id >= Max_Clause_Id then
         Ada.Text_IO.Put_Line ("Increase Container");
         Increase_Container (Id, Result);
         if Result /= Successful then
            Ada.Text_IO.Put_Line ("error: not enough memory for increasing clause storage");
            return;
         end if;
      end if;
      
      if Id /= Next_Id and then Id <= Max_Clause_Id then
         Ada.Text_IO.Put_Line ("warning: id mismatch");
         Ada.Text_IO.Put_Line (Id'Image);
         Ada.Text_IO.Put_Line (Next_Id'Image);
         Next_Id := Id;
         
         pragma Assert (Container'First = 1);
                        
      pragma Assert (Container'Last = Max_Clause_Id);
      pragma Assert (Max_Clause_Id > 0);
      pragma Assert (Next_Id <= Max_Clause_Id);
      pragma Assert (Working_Formula.Length <= SPARK.Big_Integers.To_Big_Integer (Integer (Next_Id)));
      pragma Assert (
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
     );
         
         pragma Assert (Invariant);
      end if;
      
      if Next_Id in Container'Range and then Next_Id < Max_Clause_Id and then  Next_Id < Extended_Index_Type'Last then  
         
          
         pragma Assert (for all I in 1 .. Clause_Vector.Last (Working_Formula) =>
                          Map_WFC (I) in Index_Type and then
                   Container (Map_WFC (I)).Clause /= null and then
              Clause_Vector.Get (Container => Working_Formula,
                                 Position => I)
              =
                          Container (Map_WFC (I)).Clause.all);
         
         pragma assert (for all I in 1 .. Next_Id - 1 =>
        (if Container (I).Clause /= null then 
              Map_CWF (I) <= Clause_Vector.Last (Working_Formula) and then
              Map_CWF (I) > 0 and then 
              Clause_Vector.Get (Container => Working_Formula,
                                     Position => Map_CWF (I))
                  =
                    Container (I).Clause.all));
         
         pragma Debug (Trace.Put_Line (Trace.Debug, "store clause " & C'Image & " at id =" & Next_Id'Image));
         
         Container (Next_Id).Clause := new Clause_Type' (C);
         -- Container (Id).Clause := new Clause_Type' (C);
         --
         
         
         Working_Formula := Working_Formula.Add (C);
         
         pragma Assert (for all I in 1 .. Clause_Vector.Last (Working_Formula) - 1 =>
                          Map_WFC (I) in Index_Type and then
                   Container (Map_WFC (I)).Clause /= null and then
              Clause_Vector.Get (Container => Working_Formula,
                                 Position => I)
              =
                          Container (Map_WFC (I)).Clause.all);
         
         Map_CWF (Next_Id) := Working_Formula.Last;
         Map_WFC (Working_Formula.Last) := Next_Id;
         
         Next_Id := Next_Id + 1;
         
         pragma Assert (Container (Map_WFC (Clause_Vector.Last (Working_Formula))).Clause.all = C);
         pragma Assert (Clause_Vector.Get (Working_Formula, Clause_Vector.Last (Working_Formula)) = C);
         
         pragma Assert (Clause_Vector.Get (Container => Working_Formula,
                                           Position => Map_CWF (Next_Id - 1)) = C);
         
         pragma Assert (for all I in 1 .. Clause_Vector.Last (Working_Formula) - 1 =>
                          Map_WFC (I) in Index_Type and then
                   Container (Map_WFC (I)).Clause /= null and then
              Clause_Vector.Get (Container => Working_Formula,
                                 Position => I)
              =
           Container (Map_WFC (I)).Clause.all);
         
         pragma Assert (for all I in 1 .. Clause_Vector.Last (Working_Formula) =>
                          Map_WFC (I) in Index_Type and then
                   Container (Map_WFC (I)).Clause /= null and then
              Clause_Vector.Get (Container => Working_Formula,
                                 Position => I)
              =
           Container (Map_WFC (I)).Clause.all);
     
             pragma assert (for all I in 1 .. Next_Id - 1 =>
        (if Container (I).Clause /= null then 
              Map_CWF (I) <= Clause_Vector.Last (Working_Formula) and then
         Map_CWF (I) > 0 and then 
              Clause_Vector.Get (Container => Working_Formula,
                                     Position => Map_CWF (I))
                  =
           Container (I).Clause.all));
         
         pragma Assert (for all I in Next_Id .. Container'Last =>
                          Container (I).Clause = null and Map_CWF (I) = 0);
         
                    
         Result := Successful;
      else
         Ada.Text_IO.Put_Line ("CRASH");
         if Next_Id not in Container'Range then
            Ada.Text_IO.Put_Line ("1");
         end if;
         if Next_Id >= Max_Clause_Id then
            Ada.Text_IO.Put_Line ("2");
         end if;
         if Next_Id >= Extended_Index_Type'Last then
            Ada.Text_IO.Put_Line ("3");
         end if;
         Result := Crash;
      end if;
   end Insert_Clause;
   
   -- --------------------------------------------------------------------------

   type Get_Unit_Result_Type (Found_Unit : Boolean) is
      record
         case Found_Unit is
         when True =>
            L : Literal_Type;
         when False =>
            Empty_Clause_Found : Boolean;
         end case;
      end record;
   
   -- --------------------------------------------------------------------------
   
   procedure Check_RUP_Clause
     (C      : in Clause_Type;
      Hints  : in Hint_Type;
      Result : out Operation_Result_Type)
   is
      use type SPARK.Big_Integers.Big_Integer;
      A_Length : Natural := 0;
      
      A : Assignment_Type with Ghost;
      
      
      
      A_Not_C : Assignment_Type with Ghost;
      
      function Get_Unit (C : Clause_Type)
                         return Get_Unit_Result_Type
        with Pre => FA_Assignment_Correspondance (False_Assignment, A) and then
        (for all L of C => L in -Num_Vars .. Num_Vars) and then
        False_Assignment'First = -Num_Vars and then
        False_Assignment'Last = Num_Vars,
          
        Post => (if Get_Unit'Result.Found_Unit then Unit_Reduct.Spec (C, A, Get_Unit'Result.L)) and then
        (if not Get_Unit'Result.Found_Unit and then Get_Unit'Result.Empty_Clause_Found then
           (for all L of C => Is_False (A, L)))
          
      is
         Found         : Boolean := False;
         Found_Literal : Literal_Type := 1; -- := Magic_Literal;
      begin
         for I in C'Range
         loop
            pragma Loop_Invariant (for all J in C'First .. I - 1 => not Is_True (A, C (J)));
            pragma Loop_Invariant (if not Found then (for all J in C'First .. I - 1 => Is_False (A, C (J))));
            pragma Loop_Invariant (if Found then (for all J in C'First .. I - 1 => (if C (J) /= Found_Literal then Is_False (A, C (J)))));
            pragma Loop_Invariant (if Found then Appears (C, Found_Literal));

            if False_Assignment (-C (I)) = 1 then
               -- Ada.Text_IO.Put_Line ("c the proof contains a hint that is satisfied");
               return Get_Unit_Result_Type' (Found_Unit => False, Empty_Clause_Found => False);
            end if;

            if False_Assignment (C (I)) = 1 then --Is_False (A, C (I)) then
               null;
            else
               if Found then
                  -- Ada.Text_IO.Put_Line ("c the proof contains a hit that is neither satisfied, but has at two non-false literals.");
                  return Get_Unit_Result_Type' (Found_Unit => False, Empty_Clause_Found => False);
               else
                  Found := True;
                  Found_Literal := C (I);
               end if;
            end if;
         end loop;

         if Found then
            return Get_Unit_Result_Type' (Found_Unit => True, L => Found_Literal);
         else
            return Get_Unit_Result_Type' (Found_Unit => False, Empty_Clause_Found => True);
         end if;
      end Get_Unit;
      
      procedure Repair
      is
      begin
         for I in Literal_Vectors.First (Repair_Vec) ..
           Literal_Vectors.Last (Repair_Vec)
         loop
            False_Assignment (- Literal_Vectors.Get(Repair_Vec, I)) := 0;
            A := A.Remove (Literal_Vectors.Get(Repair_Vec, I));
         end loop;
      end Repair;
      
      
   begin
      
      
      
        
      -- False_Assignment.all := (others => 0);
      pragma Assert (for all I in False_Assignment'Range => False_Assignment (I) = 0);
      
      for I in C'Range
      loop
         pragma Loop_Invariant (FA_Assignment_Correspondance (False_Assignment, A));
         pragma Loop_Invariant (Assignment_Vector.Last (A) <= I);
         pragma Loop_Invariant (Unit_Reduct.Assignment_Clause (A, C (C'First .. I - 1)));
         pragma Loop_Invariant (SPARK.Big_Integers.To_Big_Integer (A_Length) = Assignment_Vector.Length (A));
         
         if C (I) not in -Num_Vars .. Num_Vars then
            --pragma Debug (Trace.Put_Line
            --  Trace.Put_Line
            --    (Trace.Error,
            --     "clause " & C'Image & " contains the literal " & C (I)'Image &
            --       " that is beyond Num_Vars =" & Num_Vars'Image);
            --  
            ^
            Result := Failure;
            return;
         end if;
         
         if False_Assignment (-C (I)) = 1 then
            Result := Successful;
            Repair;
            return;
         end if;
         
         False_Assignment (C (I)) := 1;
         A := A.Add (- C(I));
         A_Length := A_Length + 1;
      end loop;
      
      
      pragma Assert (FA_Assignment_Correspondance (False_Assignment, A));
      A_Not_C := A;
      pragma Assert (Unit_Reduct.Assignment_Clause (A_Not_C, C));
      
      --pragma Debug (Trace.Put_Line (Trace.Trace, "hints =" & Hints'Image));
      --Trace.Put_Line (Trace.Trace, "hints =" & Hints'Image);
      
      for Hint of Hints
      loop
         pragma Loop_Invariant (FA_Assignment_Correspondance (False_Assignment, A));
         pragma Loop_Invariant (Unit_Reduct.Equivalent (Working_Formula, A'Loop_Entry, Working_Formula, A));
         pragma Loop_Invariant (A_Not_C = A'Loop_Entry);
         pragma Loop_Invariant (Unit_Reduct.Assignment_Clause (A_Not_C, C));
         pragma Loop_Invariant (SPARK.Big_Integers.To_Big_Integer (A_Length) = Assignment_Vector.Length (A));
         
         pragma Debug (Trace.Put_Line (Trace.Trace, "consider hint" & Hint'Image));
         
         -- Check whether hint is in the formula
         if not (Hint in Container'Range and then Container (Hint).Clause /= null) -- and then Hint < Next_Id)
         then
            --pragma Debug (Trace.Put_Line (Trace.Error, "hint does not exist or is in future"));
            Ada.Text_IO.Put_Line ("hint does not exist");
            Ada.Text_IO.Put_Line (Hint'Image);
            Ada.Text_IO.Put_Line (Container'Last'Image);
            --Ada.Text_IO.Put_Line (Container (Hint).Clause'Image);
            Result := Failure;
            return;
         end if;
         
         pragma Debug (Trace.Put_Line (Trace.Trace, "hint clause =" & Container (Hint).Clause.all'Image));
         
         -- Satisfy Spec of Unit_Reduct
         declare
            GUR : Get_Unit_Result_Type := Get_Unit (Container (Hint).Clause.all);
         begin
            if not GUR.Found_Unit and then not GUR.Empty_Clause_Found then
               --  Trace.Put_Line
               --    (Trace.Error,
               --     "During RUP verification of the clause " & C'Image &
               --       " the hint clause " & Container (Hint).Clause.all'Image &
               --       " with id " & Hint'Image &
               --       " does neither become unit nor conflict clause.");
               
               -- Nothing to do
               Ada.Text_IO.Put_Line ("c ignore hint id " & Hint'Image);
               null;
               
               -- Result := Failure;
               -- return;
            elsif GUR.Found_Unit then
               if A_Length < Positive'Last 
               then
                  pragma Assert (Unit_Reduct.Spec (Container (Hint).Clause.all, A, GUR.L));
                  pragma assert (Container (Hint).Clause.all = Clause_Vector.Get (Working_Formula, Map_CWF (Hint)));
                  pragma Assert (Unit_Reduct.Propagate (A, A.Add (GUR.L), Working_Formula));
                  Unit_Reduct.Propagate_Lemma (A, A.Add (GUR.L), Working_Formula);
                  
                  pragma Debug (Trace.Put_Line
                    (Trace.Trace,
                     "propagate" & GUR.L'Image));
               
                  False_Assignment (- GUR.L) := 1;
                  A := A.Add (GUR.L);
                  
                  A_Length := A_Length + 1;
                  declare
                     Success : Boolean;
                  begin
                     Literal_Vectors.Append (Repair_Vec, GUR.L, Success); -- TODO
                  end;
               else
                  Ada.Text_IO.Put_Line ("c assignment length exceeded; proof cannot be accepted.");
                  Result := Failure;
                  return;
               end if;
               
               
            elsif not GUR.Found_Unit and then GUR.Empty_Clause_Found then
               Result := Successful;
               pragma assert (Container (Hint).Clause.all = Clause_Vector.Get (Working_Formula, Map_CWF (Hint)));
               Unit_Reduct.Propagate_RUP_Lemma (A_Not_C, A, C, Working_Formula);
               Repair;
               return;
            else
               pragma Assert (False);
            end if;
         end;
      end loop;
      
      pragma Debug (Trace.Put_Line
        (Trace.Error,
         "The RUP verification of the clause " & C'Image &
           " did not detected the empty clause. "));
      
      Result := Failure;
   end Check_RUP_Clause;
   
  
   -- --------------------------------------------------------------------------
   
   procedure Delete_Clause
     (Id : in Index_Type;
      Result : out Operation_Result_Type)
   is
      procedure Free is new Ada.Unchecked_Deallocation	
        (Object => Clause_Type, Name => Clause_Pointer_Type);	
      
      Old_Working_Formula : constant Formula_Type := Working_Formula with Ghost;
      Pos : constant Natural := Map_CWF (Id) with Ghost;
      Old_Map_WFC : constant Map_WFC_Type := Map_WFC with Ghost;
      Old_Map_CWF : constant Map_CWF_Type := Map_CWF with Ghost;
   begin
      if Id < Next_Id and then Id in Container'Range and then Container (Id).Clause /= null then
         
         pragma Assert (for all I in 1 .. Clause_Vector.Last (Working_Formula) =>
                  Map_WFC (I) in Index_Type and then
                   Container (Map_WFC (I)).Clause /= null and then
              Clause_Vector.Get (Container => Working_Formula,
                                 Position => I)
              =
           Container (Map_WFC (I)).Clause.all);
     
         pragma Assert (for all I in 1 .. Next_Id - 1 =>
        (if Container (I).Clause /= null then 
                Map_CWF (I) <= Clause_Vector.Last (Working_Formula) and then
         Map_CWF (I) > 0 and then 
              Clause_Vector.Get (Container => Working_Formula,
                                     Position => Map_CWF (I))
                  =
           Container (I).Clause.all));
         
         pragma Assert (for all I in Map_CWF'Range =>
                          (for all J in Map_CWF'Range =>
                             (if I /= J and then Map_CWF (I) /= 0 then Map_CWF (I) /= Map_CWF (J))));
         
         pragma Assert (for all I in Map_WFC'Range =>
                          (for all J in Map_WFC'Range =>
                             (if I /= J and then Map_WFC (I) /= 0 then Map_WFC (I) /= Map_WFC (J))));
         
         pragma Assert (for all I in Map_WFC'Range =>
                          (if Map_WFC (I) /= 0 then 
                                Container (Map_WFC (I)).Clause /= null and then 
                           Map_CWF (Map_WFC (I)) = I));
         
         pragma Assert (for all I in Map_CWF'Range =>
                          (if Map_CWF (I) /= 0 then 
                                Map_CWF (I) <= Working_Formula.Last and then 
                                Map_WFC (Map_CWF (I)) = I));
         
         
         
         
         Working_Formula := Clause_Vector.Remove (Container => Working_Formula,
                                                  Position => Pos);
         --pragma Assert (Working_Formula = Old_Working_Formula.Remove (Map_CWF (Id)));
         Free (Container (Id).Clause);
         Container (Id).Clause := null;
         Container (Id).Deleted := True;
         
         --Map_CWF (Id) := 0;
         Map_CWF := [for I in Map_CWF'Range =>
                        (if Map_CWF (I) > 0 and then Map_CWF (I) >= Pos then
                              Map_CWF (I) - 1 else Map_CWF (I))];
         Map_CWF (Id) := 0;
         
         Map_WFC := [for I in Map_WFC'Range =>
                        (if I >= Pos and I < Old_Working_Formula.Last then
                            Map_WFC (I + 1) else Map_WFC (I))];
         Map_WFC (Old_Working_Formula.Last) := 0;
         
         pragma Assert (for all I in 1 .. Pos - 1 => Old_Map_WFC (I) = Map_WFC (I));
         pragma Assert (for all I in Pos .. Clause_Vector.Last (Working_Formula) =>
                          Old_Map_WFC (I + 1) = Map_WFC (I));
         
         pragma Assert (for all I in 1 .. Pos - 1 =>
                  Map_WFC (I) in Index_Type and then
                   Container (Map_WFC (I)).Clause /= null and then
              Clause_Vector.Get (Container => Working_Formula,
                                 Position => I)
              =
           Container (Map_WFC (I)).Clause.all);
         
         
         pragma Assert (for all I in 1 .. Clause_Vector.Last (Working_Formula) =>
                  Map_WFC (I) in Index_Type and then
                   Container (Map_WFC (I)).Clause /= null and then
              Clause_Vector.Get (Container => Working_Formula,
                                 Position => I)
              =
           Container (Map_WFC (I)).Clause.all);
     
             pragma Assert (for all I in 1 .. Next_Id - 1 =>
        (if Container (I).Clause /= null then 
                Map_CWF (I) <= Clause_Vector.Last (Working_Formula) and then
         Map_CWF (I) > 0 and then 
              Clause_Vector.Get (Container => Working_Formula,
                                     Position => Map_CWF (I))
                  =
           Container (I).Clause.all));
         
         
        pragma Assert (for all I of Map_WFC => I < Next_Id);
        pragma Assert (for all I of Map_CWF => I <= Working_Formula.Last);
      
        pragma Assert (for all I in Map_CWF'Range =>
                          (for all J in Map_CWF'Range =>
                             (if I /= J and then Map_CWF (I) /= 0 then Map_CWF (I) /= Map_CWF (J))));
         
         pragma Assert(for all I in Map_WFC'Range =>
                          (for all J in Map_WFC'Range =>
                             (if I /= J and then Map_WFC (I) /= 0 then Map_WFC (I) /= Map_WFC (J))));
         
         pragma Assert (for all I in Map_WFC'Range =>
                          (if Map_WFC (I) /= 0 then 
                                Container (Map_WFC (I)).Clause /= null and then 
                           Map_CWF (Map_WFC (I)) = I));
         
         
         Result := Successful;
      else
         Result := Failure;
         Ada.Text_IO.Put_Line ("I dont know what to delete");
      end if;
   end Delete_Clause;
   
   -- --------------------------------------------------------------------------
   
   function Get_Global_Hint (Hints : in Hint_Type)
                             return Hint_Type
   is
      Length : Natural := 0;
   begin
      for I in Hints'Range
      loop
         pragma Loop_Invariant (Length = I);
         pragma Loop_Invariant (for all J in Hints'First .. I - 1 => Hints (J) > 0);
         exit when Hints (I) <= 0;
         
         Length := Length + 1;
      end loop;
      
      declare
         C_Length : constant Natural := Length;
         Result : Hint_Type (0 .. C_Length - 1) := [for J in 0 .. C_Length - 1 => Index_Type (Hints (Hints'First + J))];
      begin
         return Result;
      end;
      
   end Get_Global_Hint;
   
   -- --------------------------------------------------------------------------
   
   function Get_Hint_Start_For_RC
     (Hints : Hint_Type;
      Id    : Index_Type)
      return Natural
   is
   begin
      for I in Hints'Range
      loop
         if Hints (I) = - Integer (Id) then
            --  Ada.Text_IO.Put_Line ("EQ");
            --  Ada.Text_IO.Put_Line ("I => " &  I'Image);
            --  Ada.Text_IO.Put_Line ("ID =>" & Id'Image);
            --  Ada.Text_IO.Put_Line ("Hints =>" & Hints'Image);
            return I;
         end if;
      end loop;
      
      return Natural'Last;
   end Get_Hint_Start_For_RC;
   
   -- --------------------------------------------------------------------------
   
   Empty_RUP_Clause_Hint : constant Hint_Type (0 .. -1) := (others => 1);
   
   function Valid_Hint (Hints : in Hint_Type) return Boolean
   is (for all X of Hints => X /= 0);
   
   function Get_Hint_End_For_RC
     (Hints : Hint_Type;
      Start : Positive)
      return Natural
     with Pre => Hints'Last > 0,
       Post => Get_Hint_End_For_RC'Result <= Hints'Last and then
             (for all I in Start .. Get_Hint_End_For_RC'Result => Hints (I) >= 0)
   is
   begin
      for I in Start .. Hints'Last
      loop
         pragma Loop_Invariant (for all J in Start .. I - 1 => Hints (J) >= 0);
         if Hints (I) < 0 then
            return I - 1;
         end if;
      end loop;
      
      return Hints'Last;
   end Get_Hint_End_For_RC;
   
   function Get_All_Hint_For_RC (Hints : Hint_Type; Id : in Index_Type) return Hint_Type
   is
   begin
      return [for I in Hints'First .. Hints'Last => (if Hints (I) > 0 then Hints (I) else 1)];
   end Get_All_Hint_For_RC;
   
   function Get_Hint_For_RC (Hints : in Hint_Type;
                             Id : in Index_Type)
                             return Hint_Type
     with Pre => Hints'Last > 0 and Valid_Hint (Hints)
   is
      Start, Stop : Natural;
   begin
      Start := Get_Hint_Start_For_RC (Hints, Id);
      if Start = Natural'Last then
         --Ada.Text_IO.Put_Line ("======== STRANGE BEHAVIOR ========");
         return Empty_RUP_Clause_Hint;
      end if;
      
      Stop := Get_Hint_End_For_RC (Hints, Start + 1);
      
      if Stop = 0 then
         --Ada.Text_IO.Put_Line ("======== STRANGE BEHAVIOR 2 ========");
         return Empty_RUP_Clause_Hint;
      end if;
      
      
      --Ada.Text_IO.Put_Line ("Hint for ID" & Id'Image);
      return [for J in Start + 1 .. Stop => (Hints (J))];
   end Get_Hint_For_RC;
   
   -- --------------------------------------------------------------------------
   
   procedure Check_RAT_Clause
     (C      : in     Clause_Type;
      Hints  : in     Hint_Type; 
      Result :    out Operation_Result_Type)
   is
      Global_Hints : Hint_Type := Get_Global_Hint (Hints);
      
      Pivot : Literal_Type := C (C'First);
   begin
      
      --  declare
      --     All_Hint_Clauses : Hint_Type := Get_All_Hint_For_RC (Hints, 1);
      --  begin
      --     Check_RUP_Clause (C, All_Hint_Clauses, Result);
      --     Ada.Text_IO.Put_Line ("Initial RUP check before RAT: " & Result'Image);
      --  end;
                     
      for Id in Container'First .. Next_Id - 1
      loop
         pragma Loop_Invariant (Invariant);
         pragma Loop_Invariant 
           (for all J in Container'First .. Id - 1 =>
              (if Container (J).Clause /= null then
                    C'Length +  Container (J).Clause.all'Length < 2 ** 16));
         pragma Loop_Invariant 
           (for all J in Container'First .. Id - 1 =>
              (if Container (J).Clause /= null then
                  C'Length + Working_Formula.Get (Map_CWF (J))'Length < 2 ** 16));
         pragma Loop_Invariant
           (for all J in Container'First .. Id - 1 =>
              (if Container (J).Clause /= null and then 
               Appears (Container (J).Clause.all, -Pivot) and then
               C'Length + Container (J).Clause.all'Length - 1 < 2 ** 16
               then
                  Strong_RAT.Consequence (Working_Formula, Weak_Resolution.Resolve (C, Container (J).Clause.all, Pivot))));
         -- translation to working formula
         pragma Loop_Invariant
           (for all J in Container'First .. Id - 1 =>
              (if Container (J).Clause /= null and then 
               Appears (Working_Formula.Get (Map_CWF (J)), -Pivot) and then
               C'Length + Working_Formula.Get (Map_CWF (J))'Length - 1 <= 2 ** 16
               then
                  Strong_RAT.Consequence (Working_Formula, Weak_Resolution.Resolve (C, Working_Formula.Get (Map_CWF (J)), Pivot))));
         
         if Container (Id).Clause /= null and then C'Length + Container (Id).Clause.all'Length >= 2 ** 16 then
            pragma Debug (Ada.Text_IO.Put_Line ("Cannot resolve; aborting RAT check"));
            Result := Crash; -- Failure
            return;
         end if;
         
         if Container (Id).Clause /= null and then 
           Appears (Container (Id).Clause.all, -Pivot)
         then
            --Ada.Text_IO.Put_Line ("ID " & Id'Image);
            --Ada.Text_IO.Put_Line ("consider clause for RUP check " & Container(Id).Clause.all'Image);
            
            declare
               RUP_Hint   : Hint_Type := Global_Hints & (if Valid_Hint (Hints) and then Hints'Last > 0 then Get_Hint_For_RC (Hints, Id) else []);
               -- RUP_Hint   : Hint_Type := Global_Hints & (if Valid_Hint (Hints) and then Hints'Last > 0 then Get_All_Hint_For_RC (Hints, Id) else []);
               
               Resolvent  : Clause_Type := Weak_Resolution.Resolve (C, Container (Id).Clause.all, Pivot);
               RUP_Result : Operation_Result_Type;
            begin
               --  Ada.Text_IO.Put_Line ("resolvent " & Resolvent'Image);
               --  Ada.Text_IO.Put_Line ("Global hint:" & Global_Hints'Image);
               --  Ada.Text_IO.Put_Line ("Validity:" & Valid_Hint (Hints)'Image);
               --  if Hints'Last > 0 then
               --     Ada.Text_IO.Put_Line ("Hints'Last > 0  => TRUE");
               --  else
               --     Ada.Text_IO.Put_Line ("Hints'Last > 0  => FALSE");
               --  end if;
               --  Ada.Text_IO.Put_Line ("RUP hint " & RUP_Hint'Image);
               
               Check_RUP_Clause (Resolvent, RUP_Hint, RUP_Result);
               
               if RUP_Result = Crash then
                  Ada.Text_IO.Put_Line ("c RUP check crashed");
                  Result := Crash;
                  return;
                  
               elsif RUP_Result = Failure then 
                  Ada.Text_IO.Put_Line ("c RUP check failed");
                  pragma Assert (Invariant);
                  
                  Result := Crash; -- Failure
                  return;
               end if;
               
               pragma Assert (Strong_RAT.Consequence (Working_Formula, Weak_Resolution.Resolve (C, Container (Id).Clause.all, Pivot)));
               pragma Assert (Container (Id).Clause.all = Working_Formula.Get (Map_CWF (Id)));
               Weak_Resolution.Workaround_Resolve_Equality (C, Container (Id).Clause.all, Working_Formula.Get (Map_CWF (Id)), Pivot);
               pragma Assert (Equivalent (Weak_Resolution.Resolve (C, Container (Id).Clause.all, Pivot),
                              Weak_Resolution.Resolve (C, Working_Formula.Get (Map_CWF (Id)), Pivot)));
               pragma Assert (Strong_RAT.Consequence (Working_Formula, Weak_Resolution.Resolve (C, Working_Formula.Get (Map_CWF (Id)), Pivot)));
            end;
         end if;
      end loop;
      
      pragma Assert (for all D of Working_Formula => C'Length + D'Length < 2 ** 16);
      
      
      pragma Assert (Strong_RAT.Spec (Working_Formula, C, Pivot));
      Strong_RAT.Lemma (Working_Formula, C, Pivot);
      
      Result := Successful;
   end Check_RAT_Clause;
   
   -- --------------------------------------------------------------------------
   
   function Get_Max_Variable (C : Clause_Type) return Natural
     with Post => (for all L of C => L in -Get_Max_Variable'Result .. Get_Max_Variable'Result)
   is
      Current_Max : Natural := 0;
   begin
      for I in C'First .. C'Last
      loop
         pragma Loop_Invariant (for all J in C'First .. I - 1 => C (J) in -Current_Max .. Current_Max);
         
         declare
            L : Literal_Type := C (I);
         begin
            
            if L > 0 and then L > Current_Max then
               Current_Max := Natural (L);
            elsif L < 0 and then -L > Current_Max then
               Current_Max := Natural (-L);
            end if;
         end;
      end loop;
      
      return Current_Max;
   end Get_Max_Variable;
   
   -- --------------------------------------------------------------------------
   
   procedure Increase_Num_Vars
     (New_Num_Vars : Natural;
      Result : out Operation_Result_Type)
   is
   begin
      Free_Assignment (False_Assignment);
      Num_Vars := New_Num_Vars;
      False_Assignment := new Integer_Array'([for I in -Num_Vars .. Num_Vars => 0]);
      
      if False_Assignment /= null then
         Result := Successful;
      else
         Result := Failure;
      end if;
   end Increase_Num_Vars;
   
   -- --------------------------------------------------------------------------
   
   procedure Increase_Container
     (Minimum : in     Natural;
      Result   :    out Operation_Result_Type)
   is
   begin
      if Container.all'Last > 2**29
      then
         Ada.Text_IO.Put_Line ("c ERROR memory exhausted.");
         Result := Failure;
      else
         pragma Assert (Container.all'Last > 0);
         pragma Assert (Container.all'Last * 2 > 0);
         pragma Assert (Container.all'Last * 2 > Container.all'Last);
         
         declare
            New_Size : Index_Type := 
              (if Minimum < Container.all'Last * 2 
               then Container.all'Last * 2
                 else Minimum);
            
            New_Container : Container_Access_Type := 
              new Container_Type'
                (for J in 1 .. New_Size => 
                       Entry_Type'(Deleted => False, Clause => null));
         begin
            Ada.Text_IO.Put_Line
              ("c increasing clause container from " & 
                 Container'Last'Image &
                 " to "&
                 New_Container'Last'Image &
                 " clauses.");
            
            New_Container.all (1 .. Next_Id) := Container.all (1 .. Next_Id);
            
            Max_Clause_Id := New_Container.all'Last;
            Free_Container (Container);
            
            Container := New_Container;
            
            pragma Assert (for all I in Next_Id .. Container'Last =>
              Container (I).Clause = null and Map_CWF (I) = 0);
            
            Result := Successful;
         end;
      end if;
      
   end Increase_Container;
     
   -- --------------------------------------------------------------------------
   
   procedure Parse_Formula
     (Filename : in String;
      Result : out Operation_Result_Type)
   is
      File : Ada.Text_IO.File_Type;
      S    : Boolean;
      Id   : Natural := 1;
      Number_Clauses, Number_Variables : Natural;
      Line : String (1 .. 2 ** 16 - 1) with Relaxed_Initialization; 
      
      LV : Literal_Vectors.Vector;

      Init_Vectors_Success : Boolean;
      IR : Operation_Result_Type;
      
      use type Literal_Vectors.Extended_Index_Type;
      use type Literal_Vectors.Index_Type;
      use type Ada.Text_IO.File_Mode;
   begin
      --IR := Failure;
      
      begin
         LV.Init (Init_Vectors_Success);
         if not Init_Vectors_Success then
            Result := Failure;
            Ada.Text_IO.Put_Line ("initial vector initialization failed");
            return;
         end if;
      
      
         Ada.Text_IO.Open
           (File, Mode => Ada.Text_IO.In_File, Name => Filename);
      
         declare
            --Line : String; -- := Ada.Text_IO.Get_Line (File);
            Last : Natural;
         begin
            Ada.Text_IO.Get_Line (File => File, Item => Line, Last => Last);
         
            Parsing.Consume_PCNF_Line (Line (1 .. Last), Number_Clauses, Number_Variables, S);
      
            if not S then
               Ada.Text_IO.Put_Line ("could not parse p cnf header");
               Result := Failure;
               return;
            end if;
         end;
      
         Init (Number_Clauses => Extended_Index_Type (Number_Clauses),
               Number_Variables =>  Number_Variables,
               Result => IR);
      
         if IR /= Successful then
            Ada.Text_IO.Put_Line ("Error initialization");
            Result := Failure;
            return;
         end if;
      
         while not Ada.Text_IO.End_Of_File (File)
         loop
            pragma Loop_Invariant (Ada.Text_IO.Mode (File) = Ada.Text_IO.In_File);
            pragma Loop_Invariant (Ada.Text_IO.Is_Open (File));
            pragma Loop_Invariant (LV.Is_Valid);
            pragma Loop_Invariant (Invariant);
            pragma Loop_Variant (Decreases => Integer'Last - Id);
           
         
            declare
               Last : Natural;
               C : Natural := 1;
            begin
               if Id = Natural'Last then
                  Ada.Text_IO.Put_Line ("Too many clauses");
                  Result := Failure;
                  return;
               end if;
               
               Ada.Text_IO.Get_Line (File => File, Item => Line, Last => Last);
            
               Parsing.Consume_Clause (Line (1 .. Last), True, C, LV, S);
            
               if not S then
                  Ada.Text_IO.Put_Line ("Error parsing line " & Id'Image);
                  Result := Failure;
                  return;
               end if;
               
               if Natural (LV.Last) - 1 >= 2**16 then
                  Ada.Text_IO.Put_Line ("too long clause " & Id'Image);
                  Result := Failure;
                  return;
               end if;
            
               declare
                  C : Clause_Type := [for J in 0 .. Natural (LV.Last) - 1 => LV.Get (Literal_Vectors.Index_Type (J + 1))];
               begin
                  if Get_Max_Variable (C) > Num_Vars then
                     Increase_Num_Vars (Get_Max_Variable (C), IR);
                     
                     if IR /= Successful then
                        Ada.Text_IO.Put_Line ("could not increase number variables");
                        Result := Failure;
                        return;
                     end if;
                  end if;
                  
                  Insert_Clause (C => C, Id => Extended_Index_Type (Id), Result => IR);
               
                  if IR /= Successful then
                     Ada.Text_IO.Put_Line ("Error inserting clause");
                     Ada.Text_IO.Put_Line (Id'Image);
                     Result := Failure;
                     return;
                  end if;
               end;
            
               Id := Id + 1;
            end;
         end loop;
      
         Ada.Text_IO.Close (File);
         
         Input_Formula := Working_Formula;
      
         Result := Successful;
         
      exception
         when others => -- E : Ada.Text_IO.Name_Error =>
            Ada.Text_IO.Put_Line ("Some error appeared");
            Result := Failure;
      end;
      
      --LV.Free;
      --IV.Free;
   end Parse_Formula;
   
   -- --------------------------------------------------------------------------  
   
   
   procedure Helper_Lemma
     (F, G : Formula_Type)
     with Pre => F = G,
     Post => Equisatisfiable (F, G),
       Ghost
   is
   begin
      null;
   end Helper_Lemma;
       
   
   procedure Check_Proof
     (Filename : in String;
      Result : out Operation_Result_Type)
   is
   
      File : Ada.Text_IO.File_Type;
      S : Boolean;
      Id : Natural := 1;
      Line : String (1 .. 2 ** 16 - 1) with Relaxed_Initialization; 
      
      LV : Literal_Vectors.Vector;
      pragma Annotate (GNATprove, False_Positive, "resource or memory leak might occur", "Intentional");
      
      IV : Integer_Vectors.Vector;
      pragma Annotate (GNATprove, False_Positive, "resource or memory leak might occur", "Intentional");
      
      Init_Vectors_Success : Boolean;
      Empty_Clause_Detected : Boolean := False;
      Intermediate_Formula : Formula_Type with Ghost;
      
      IR : Operation_Result_Type;
      
      procedure Init_Vectors
      is
      begin
         LV.Init (Init_Vectors_Success);
         if Init_Vectors_Success then
            IV.Init (Init_Vectors_Success);
         end if;
         Literal_Vectors.Init (Repair_Vec, Init_Vectors_Success);
      end Init_Vectors;
      
      use type Literal_Vectors.Extended_Index_Type;
      use type Literal_Vectors.Index_Type;
      use type Ada.Text_IO.File_Mode;
      use type Integer_Vectors.Extended_Index_Type;
   begin
      Result := Failure;
      
      begin
         Init_Vectors;
         if not Init_Vectors_Success then
            Result := Failure;
            Ada.Text_IO.Put_Line ("initial vector initialization failed");
            return;
         end if;
      
      
         Ada.Text_IO.Open
           (File, Mode => Ada.Text_IO.In_File, Name => Filename);
      
      
      
         while not Ada.Text_IO.End_Of_File (File)
         loop
            pragma Loop_Invariant (Ada.Text_IO.Mode (File) = Ada.Text_IO.In_File);
            pragma Loop_Invariant (Ada.Text_IO.Is_Open (File));
            pragma Loop_Invariant (LV.Is_Valid);
            pragma Loop_Invariant (IV.Is_Valid);
            pragma Loop_Invariant (Invariant);
            pragma Loop_Variant (Decreases => Integer'Last - Id);
            pragma Loop_Invariant (Unsat_Preservation (Input_Formula, Working_Formula));
            pragma Loop_Invariant (if Empty_Clause_Detected then not Satisfiable (Input_Formula));
           
         
            declare
               Last : Natural;
               C : Natural;
               Obtained_Id : Natural;
               Deletion_Step : Boolean;
            begin
               if Id = Natural'Last then
                  Ada.Text_IO.Put_Line ("Too many clauses");
                  Result := Failure;
                  return;
               end if;
               
               Ada.Text_IO.Get_Line (File => File, Item => Line, Last => Last);
               
               if Last = Line'Last then
                  Ada.Text_IO.Put_Line ("Expect parsing error");
               end if;
               
               Parsing.Consume_Partial_LRAT_Step (Line (1 .. Last), Obtained_Id, C, Deletion_Step, S);
            
               if not S then
                  Ada.Text_IO.Put_Line ("1 Error parsing line " & Id'Image);
                  Ada.Text_IO.Put_Line (Line (1 .. Last));
                  Result := Failure;
                  return;
               end if;
               
               if Deletion_Step and then C < 2 ** 16 then
                  Parsing.Consume_LRAT_Delete_Line (Line (1 .. Last), C, IV, S);
                  
                  if not S then
                     Ada.Text_IO.Put_Line ("2 Error parsing line " & Id'Image);
                     Result := Failure;
                     return;
                  end if;
                  
                  for I of IV.All_Elems
                  loop
                     pragma Loop_Invariant (Invariant);
                     pragma Loop_Invariant (Unsat_Preservation (Input_Formula, Working_Formula));
                     
                     if I > 0  then
                        Delete_Clause (Index_Type (I), IR);
                        
                        if IR /= Successful then
                           Result := Failure;
                           Ada.Text_IO.Put_Line ("Could not apply deletion");
                           return;
                        end if;
                     else
                        Ada.Text_IO.Put_Line ("deletion id not in range");
                        Result := Failure;
                        return;
                     end if;
                     
                  end loop;
               elsif not Deletion_Step and then C < 2 ** 16 then 
                  Parsing.Consume_LRAT_Learn_Line (Line (1 .. Last), C, LV, IV, S);
                  
                  if not S then
                     Ada.Text_IO.Put_Line ("3 Error parsing line " & Id'Image);
                     Ada.Text_IO.Put_Line ("START");

                     Ada.Text_IO.Put_Line (Line (1 .. Last));
                     Ada.Text_IO.Put_Line ("END");
                     Result := Failure;
                     return;
                  end if;
                  
                  if Natural (LV.Last) - 1 >= 2**16 then
                     Ada.Text_IO.Put_Line ("too long clause " & Id'Image);
                     Result := Failure;
                     return;
                  end if;
                  
                  if Next_Id >= Container'Last then
                     Increase_Container (Next_Id, IR);
                     if IR /= Successful then
                        Ada.Text_IO.Put_Line ("Error increasing container");
                        Result := Failure;
                        return;
                     end if;
                  end if;
                  
                  if IV.Last >= 2**15 then
                        Ada.Text_IO.Put_Line ("Too long hints");
                     Result := Failure;
                     return;
                  end if;	
            
                  declare
                     C : Clause_Type := [for J in 0 .. Natural (LV.Last) - 1 => LV.Get (Literal_Vectors.Index_Type (J + 1))];
                     Successful_Check : Boolean := False;
                     Hints : Hint_Type := [for J in 0 .. Natural (IV.Last) - 1 => 1]; -- := (others => 1);
                  begin
                     if Get_Max_Variable (C) > Num_Vars then
                        Increase_Num_Vars (Get_Max_Variable (C), IR);
                     
                        if IR /= Successful then
                           Ada.Text_IO.Put_Line ("could not increase number variables");
                           Result := Failure;
                           return;
                        end if;
                     end if;
                     
                     for J in 0 .. Natural (IV.Last) - 1
                     loop
                        -- NEEDED ??
                        if IV.Get (Integer_Vectors.Index_Type (J + 1)) = 0 -- not in 1 .. Natural'Last
                        then
                           Ada.Text_IO.Put_Line ("Hints not in range");
                           Ada.Text_IO.Put_Line (J'Image);
                           Ada.Text_IO.Put_Line (Line (1 .. Last));
                           Ada.Text_IO.Put_Line (IV.Get (Integer_Vectors.Index_Type (J + 1))'Image);
                           --Result := Failure;
                           --return;
                        end if;
                           
                        Hints (J) := IV.Get (Integer_Vectors.Index_Type (J + 1));
                     end loop;
                     
                     if (for all X in 1 .. IV.Last => IV.Get (X) > 0)
                     then                        
                        Check_RUP_Clause (C, Hints, IR);
                           
                        if IR = Successful then
                           Successful_Check := True;
                        else
                           Ada.Text_IO.Put_Line ("RUP failed");
                           --Ada.Text_IO.Put_Line (C'Image);
                           --Ada.Text_IO.Put_Line (Hints'Image);
                           --Ada.Text_IO.Put_Line (Obtained_Id'Image);
                           --Ada.Text_IO.Put_Line ("TODO: We assume that RAT clauses have at least one negative hint present in the proof.");
                           --return;
                           null;
                        end if;
                     end if;
                     
                     if not (for all X in 1 .. IV.Last => IV.Get (X) > 0) and then not Successful_Check -- TODO
                     then   
                        Check_RAT_Clause (C, Hints, IR);
                        
                        if IR = Successful then
                           Successful_Check := True;        
                        else
                           Ada.Text_IO.Put_Line ("RAT check failed");
                        end if;
                     end if;
                     
                     pragma Assert (if Successful_Check then Unsat_Preservation (Working_Formula, Working_Formula.Add (C)));
                     
                     if not Successful_Check then
                        Ada.Text_IO.Put_Line ("clause verification failed");
                        Ada.Text_IO.Put_Line (Obtained_Id'Image);
                       
                        Result := Failure;
                        return;
                     end if;
                     
                     pragma Assert (Unsat_Preservation (Input_Formula, Working_Formula));
                     pragma Assert (Unsat_Preservation (Working_Formula, Working_Formula.Add (C)));
                     pragma Assert (Unsat_Preservation (Input_Formula, Working_Formula.Add (C)));
                     
                     Intermediate_Formula := Working_Formula;
                     
                     if Obtained_Id /= Next_Id then
                        Ada.Text_IO.Put_Line ("Obtained ID:" & Obtained_Id'Image);
                        Ada.Text_IO.Put_Line ("Expected ID:" & Next_Id'Image);
                     end if;
                     
                  
                     Insert_Clause (C => C, Id => Extended_Index_Type (Obtained_Id), Result => IR);
               
                     if IR /= Successful then
                        Ada.Text_IO.Put_Line ("Error inserting clause");
                        Ada.Text_IO.Put_Line (Id'Image);
                        Result := Failure;
                        return;
                     end if;
                     
                     
                     
                     
                     -- Helper_Lemma (Working_Formula, Intermediate_Formula.Add (C), Input_Formula);
                     
                     pragma Assert (Unsat_Preservation (Input_Formula, Intermediate_Formula));
                     pragma Assert (Unsat_Preservation (Intermediate_Formula, Intermediate_Formula.Add (C)));
                     pragma Assert (Unsat_Preservation (Input_Formula, Intermediate_Formula.Add (C)));
                     pragma Assert (Working_Formula = Intermediate_Formula.Add (C));
                         
                     Helper_Lemma (Working_Formula, Intermediate_Formula.Add (C));
                     
                     
                     pragma Assert (Unsat_Preservation (Input_Formula, Working_Formula));
                     
                     if C'Length = 0 then
                        Empty_Clause_Detected := True;
                        pragma Assert (not Satisfiable (Working_Formula));
                        pragma Assert (not Satisfiable (Input_Formula));
                     end if;
               end;
                     
                     
                     
                                       
               else
                  Ada.Text_IO.Put_Line ("Parsing error");
                  Result := Failure;
                  return;
               end if;
                  
               
            end;
            
            Id := Id + 1;
         end loop;
      
         Ada.Text_IO.Close (File);
            
         if Empty_Clause_Detected then
            Result := Successful;
         else
            Result := Failure;
         end if;
         
      exception
         --  when E : Ada.Text_IO.Name_Error =>
         --        Ada.Text_IO.Put_Line ("EXCEPTION");
         --        Ada.Text_IO.Put_Line (Ada.Exceptions.Exception_Message(E));
         --  
         when others => -- E : Ada.Text_IO.Name_Error =>
            Ada.Text_IO.Put_Line ("ERROR: Exception, possibly IO error");
            --Ada.Exceptions.E
      end;
      
      -- LV.Free;
      -- IV.Free;
   end Check_Proof;

   -- --------------------------------------------------------------------------
   
   procedure Check
     (Formula_Filename : in     String;
      Proof_Filename   : in     String;
      Result           :    out Operation_Result_Type)
   is
   begin
      Ada.Text_IO.Put_Line ("c parse CNF");
      Parse_Formula (Formula_Filename, Result);
      if Result = Successful then
         Ada.Text_IO.Put_Line ("c parse and check proof");
         Check_Proof (Proof_Filename, Result);
      else
         Ada.Text_IO.Put_Line ("c parsing failed.");
      end if;
   end Check;

end SAT.LRAT;
