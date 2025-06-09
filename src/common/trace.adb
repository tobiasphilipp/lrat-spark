with Ada.Text_IO;

package body Trace 
  with SPARK_Mode
is

   procedure Put_Line
     (Level       : in Level_Type;
      Line        : in String;
      Indentation : in Natural := 0;
      Enclosing   : in String := GNAT.Source_Info.Enclosing_Entity;
      Src_Info    : in String := GNAT.Source_Info.Source_Location)
   is
      Indentation_Str : String (1 .. Indentation) := (others => ' ');
   begin
      pragma Warnings (Off, "warning: statement has no effect");
       if Level >= Configured_Level then 
         if Level in Trace .. Debug then
            Ada.Text_IO.Put_Line ("c [" & Level'Image & "/" & Enclosing & " " & Src_Info & "] " & Indentation_Str & Line);
         else
            Ada.Text_IO.Put_Line ("c [" & Level'Image & "] " & Indentation_Str & Line);
         end if;
      end if;
      pragma Warnings (On, "warning: statement has no effect");
   end Put_Line;

end Trace;
