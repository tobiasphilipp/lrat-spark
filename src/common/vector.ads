------------------------------------------------------------------------------
--                                                                          --
-- A verified proof checker written in SPARK 2014                           --
--                                                                          --
------------------------------------------------------------------------------
--                                                                          --
-- Copyright (C) 2021-2023, Tobias Philipp                                  --
--                                                                          --
------------------------------------------------------------------------------

pragma Ada_2022;
pragma Extensions_Allowed (On);
pragma Unevaluated_Use_Of_Old (Allow);

generic		
   type Element_Type is (<>);			
   Magic_Element :  Element_Type;
package Vector			
with Spark_Mode => On	
is			
   type Extended_Index_Type is new Natural;
   subtype Index_Type is Extended_Index_Type range Extended_Index_Type'First + 1 .. Extended_Index_Type'Last;
     -- range 0 .. <>
   type T_Array is array (Index_Type range 1 .. <>) of Element_Type;	
   
   Empty_Model : constant T_Array (1 .. 0) := (others => Magic_Element);
   
   function Equivalant (L, R: T_Array) return Boolean
   is ((for all E of L => (for some X of R => E = X)) and
         (for all E of R => (for some X of L => E = X)));
   
   function Subset (L, R: T_Array) return Boolean
   is (for all E of L => (for some X of R => E = X));
   
       
   function Contains (L : T_Array; E : Element_Type) return Boolean
   is (for some X of L => E = X);
   
   
   
   type Vector is limited private;
       
   function Is_Valid (V : Vector) return Boolean;		
   
   function First (V : Vector) return Extended_Index_Type
     with Inline,
     Pre => Is_Valid (V);
   
   function Last (V : Vector) return Extended_Index_Type
     with Inline,
     Pre => Is_Valid (V);
   
   function Model (V : Vector) return T_Array
     with 
       Ghost,
       Pre => Is_Valid (V);
   
   function All_Elems (V : Vector) return T_Array
     with Pre => Is_Valid (V);
   --
      
   procedure Init (V : out Vector; Success : out Boolean)	
     with	    	 
       Inline,
       Post => (if Success then Is_Valid (V) and then Model (V) = Empty_Model);
   
   procedure Free (V : in out Vector)
     with Inline;
  
   procedure Append (V : in out Vector; Elem : in Element_Type; Success : out Boolean)	
     with	    
       Inline,
       Pre => Is_Valid (V),
       Post => (if Success then
                  Is_Valid (V) and then Model (V)'Old & Elem = Model(V) and then
                  First (V)'Old = First (V) and then 
                  Last (V)'Old + 1 = Last (V) and then
                    Subset (Model (V)'Old, Model(V)));
  
   procedure Clear (V : in out Vector)	
     with	    
       Inline,
       Pre => Is_Valid (V),
       Post => Is_Valid (V) and then Model (V) = Empty_Model;
  	
   function Get (V : in Vector; Index : Index_Type) return Element_Type	
     with Inline, Pre => Is_Valid (V) and then
     Index in First (V) .. Last (V),
     Post => Model (V) (Index) = Get'Result;
       
      	   
   procedure Set_Next (V : in out Vector; Next : in Extended_Index_Type)	
     with	    	     
       Inline,	
       Pre => Is_Valid (V) and then Next <= Last (V) + 1 and then Next >= First (V),
     Post => Is_Valid (V) and then 
     First (V)'Old = First (V) and then
     Last (V) = Next - 1 and then
     Model (V) = Model (V)'Old (Model (V)'First .. Next - 1);
      
private	
   
   type T_Array_Ptr is access T_Array;  
		
   type Vector is  record		
      Data : T_Array_Ptr := null;
      Next : Extended_Index_Type := 0;
   end record;

   -- Implementation 
      
   function Is_Valid (V : Vector) return Boolean is 
     (V.Data /= null and then
      V.Data'First = 1 and then
      V.Next in V.Data'Range);	
  	   
   function Valid_Index (V : Vector; Index : Index_Type) return Boolean is (Index in V.Data'First .. V.Next - 1)
     with Inline, Pre => Is_Valid (V);
   
   function Get (V : in Vector; Index : Index_Type) return Element_Type		
   is (V.Data (Index));
   
   -- private 
   
   procedure Double (V : in out Vector; Success : out Boolean)	
     with	    
       Inline,
       Pre => Is_Valid (V),
       Post => (if Success then Is_Valid (V) and then Model (V)'Old = Model(V) and then not Is_Full (V));
   
   function Is_Full (V : Vector) return Boolean is
     (V.Data'Last <= V.Next)
     with Inline, PRe => Is_Valid (V);
   
   function Is_Empty (V : in Vector) return Boolean is (V.Next = 0)  with Inline, Pre => Is_Valid (V);
   
   function Model (V : Vector) return T_Array is 
     (declare
      Result : constant T_Array (1 .. V.Next - 1) := V.Data (V.Data'First .. V.Next - 1);
      begin
      Result);
   
   function All_Elems (V : Vector) return T_Array is 
     (declare
      Result : constant T_Array (1 .. V.Next - 1) := V.Data (V.Data'First .. V.Next - 1);
      begin
      Result);
   
   
   function First (V : Vector) return Extended_Index_Type
     is (1);
   
   function Last (V : Vector) return Extended_Index_Type
     is (V.Next - 1);
  		        
end Vector;
