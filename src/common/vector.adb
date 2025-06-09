------------------------------------------------------------------------------
--                                                                          --
-- A verified proof checker written in SPARK 2014                           --
--                                                                          --
------------------------------------------------------------------------------
--                                                                          --
-- Copyright (C) 2021-2023, Tobias Philipp                                  --
--                                                                          --
------------------------------------------------------------------------------

pragma Unevaluated_Use_Of_Old (Allow);

with Ada.Unchecked_Deallocation;		
with Ada.Text_Io;     				
     
package body Vector	
with Spark_Mode => On	
is 
   
   procedure Delete_T_Array is new Ada.Unchecked_Deallocation (T_Array, T_Array_Ptr);      
   
   -- --------------------------------------------------------------------------	
       
   procedure Init (V : out Vector; Success : out Boolean)	
   is	    
   begin			
      V.Data := new T_Array'([for J in 1 .. 4 => Magic_Element]);
      V.Next := V.Data'First;
      Success := V.Data /= null;      
   end Init;   
  
   -- --------------------------------------------------------------------------	
   
   procedure Free (V : in out Vector)
   is
   begin
      if (V.Data /= null) then
         Delete_T_Array (V.Data);
      end if;
   end Free;
   
   -- --------------------------------------------------------------------------	
          
   
  	
procedure Double (V : in out Vector; Success : out Boolean)	
   is	    	   
   begin	     
      if V.Data'Last > 2**30 then
         Success := False;
      else
         pragma Assert (V.Data'Last > 0);
         pragma Assert (Float (V.Data'Last) * 1.5 > 0.0);
         pragma Assert (Integer (Float (V.Data'Last) * 1.5) > Integer (V.Data'Last));
         
         declare
            New_Data : T_Array_Ptr := new T_Array'(for J in 1 .. Index_Type (Float (V.Data'Last) * 1.5) => Magic_Element);
         begin
            New_Data.all (1 .. V.Next) := V.Data.all (1 .. V.Next);	
            Delete_T_Array (V.Data);
            V.Data := New_Data;		
            Success := True;
         end;
      end if;
   end Double;			
  
   -- --------------------------------------------------------------------------		
  
procedure Append (V : in out Vector; Elem : in Element_Type; Success : out Boolean)	
is	     
begin	    
   if Is_Full (V) then	
      declare
         Double_Success : Boolean;
      begin
         
         Double (V, Double_Success); 
         
         if not Double_Success then
            Success := False;
            return;
         end if;
      end;
   end if;  
      
   V.Data.all (V.Next) := Elem;	
      V.Next := V.Next + 1;  
      Success := True;
end Append;	
  
   -- --------------------------------------------------------------------------  
      
   procedure Clear (V : in out Vector)	
   is	    
   begin		
      V.Next := V.Data'First;
   end Clear;				
  
   -- --------------------------------------------------------------------------  
      
   --  procedure Set (V : in out Vector; Index : in Index_Type; Elem : in Element_Type)
   --  is
   --  begin
   --     V.Data (Index) := Elem;
   --  end Set;
  
   -- --------------------------------------------------------------------------		
  
   procedure Set_Next (V : in out Vector; Next : in Extended_Index_Type)	
   is	    
   begin		
      V.Next := Next;
   end Set_Next;    
end Vector;
