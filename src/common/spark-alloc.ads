-- see discussion https://github.com/AdaCore/ada-spark-rfcs/issues/78

generic
   type Object is limited private;
   type Name is access Object;
   
package SPARK.Alloc 
  with SPARK_Mode
is

   function Alloc return Name;

   procedure Free (Ptr : in out Name)
     with Post    => Ptr = null,
          Depends => (Ptr  => null,
                      null => Ptr);

end SPARK.Alloc;
