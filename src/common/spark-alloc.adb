with Ada.Unchecked_Deallocation;


package body SPARK.Alloc 

  with SPARK_Mode
is

   function Alloc return Name is
      pragma SPARK_Mode (Off); -- Only the allocation has to be in SPARK off
   begin
      return new Object;
   exception
      when Storage_Error =>
         return null;
   end Alloc;

   procedure Free (Ptr : in out Name) is
      procedure Dealloc is new Ada.Unchecked_Deallocation (Object, Name);
   begin
      Dealloc (Ptr);
   end Free;
end SPARK.Alloc;
