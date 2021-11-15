// Java Program to print Multiplication of two floating
// point Number.
  
import java.io.*;
  
class GFG {
    public static void main(String[] args)
    {
  
        // f is to ensures that numbers are float DATA TYPE
        float f1 = 1.5f;
        float f2 = 2.0f;
  
        // to store the multiplied value
        float p = f1 * f2;
  
        // to print the product
        System.out.println("The product is: " + p);
    }
}

class GFG2 {
	   
    // Function to find the biggest of three numbers
    static int biggestOfThree(int x, int y, int z)
    {
 
        return z > (x > y ? x : y) ? z : ((x > y) ? x : y);
    }
 
    // Main driver function
    public static void main(String[] args)
    {
 
        // Declaring variables for 3 numbers
        int a, b, c;
 
        // Variable holding the largest number
        int largest;
        a = 5;
        b = 10;
        c = 3;
        // Calling the above function in main
        largest = biggestOfThree(a, b, c);
 
        // Printing the largest number
        System.out.println(largest
                           + " is the largest number.");
    }
}


//Main class
class GFG3 {

 // Main driver method
 public static void main(String[] args)
 {
     // Declaring and initializing variable to
     // Size of the pyramid
     int number = 7;

     int i = number, j;

     // Nested while loops
     // Outer loop

     // Till condition holds true
     while (i > 0) {
         j = 0;

         // Inner loop
         // Condition check
         while (j++ < number - i) {
             // Print whitespaces
             System.out.print(" ");
         }

         j = 0;

         // Inner loop
         // Condition check
         while (j++ < (i * 2) - 1) {
             // Print star
             System.out.print("*");
             while (j++ < (i * 2) - 1) {
                 // Print star
                 System.out.print("*");
                 while (j++ < (i * 2) - 1) {
                     // Print star
                     System.out.print("*");
                     while (j++ < (i * 2) - 1) {
                         // Print star
                         System.out.print("*");
                         while (j++ < (i * 2) - 1) {
                             // Print star
                             System.out.print("*");
                             while (j++ < (i * 2) - 1) {
                                 // Print star
                                 System.out.print("*");
                                 
                             }
                         }
                     }
                 }
             }
         }

         // By now, we reach end of execution for one row
         // so next line
         System.out.println();

         // Decrementing counter because we want to print
         // reverse of pyramid
         i--;
     }
 }
}