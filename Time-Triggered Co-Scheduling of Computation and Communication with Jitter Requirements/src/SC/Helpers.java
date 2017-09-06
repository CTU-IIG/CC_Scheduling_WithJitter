package SC;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.Stack;

public class Helpers {
    //------------constants-------------
    public static final double EPS = 1.0E-4;
    public static final String outputFileForCplex = "outputCPLEX.txt";
    public static final String outputFile = "output/output.txt";
    public static final String outputFileForZJExperiment = "outputExpWithDifPercentsOfZJActivities.txt";
    public static final String outputFileForExperimentWithDifPeriods = "outputExpWithDifPeriods.txt";
    public static final String CANUseCaseFile = "Use_case_CAN.txt";
    public static final String outputFileForModels = "mod.lp";
    
    //------------functions--------------
    public static void InitializeTo(double[][] array, double value){
        for(int i = 0; i < array.length; i++) {
            for(int j = 0; j < array[i].length; j++) {
                array[i][j] = value;
            }
        }
    }
    
    public static void InitializeTo(long[] array, int value){
        for (int i = 0; i < array.length; i++) {
            array[i] = value;
        }
    }
    
    public static void InitializeTo(int[] array, int value){
        for (int i = 0; i < array.length; i++) {
            array[i] = value;
        }
    }
    
    public static void InitializeTo(boolean[] array, boolean value){
        for (int i = 0; i < array.length; i++) {
            array[i] = value;
        }
    }
    
    public static void InitializeTo(double[] array, double value){
        for (int i = 0; i < array.length; i++) {
            array[i] = value;
        }
    }
    
    public static void InitializeTo(double[] array, double value, int indexStart, int indexEnd){
        for (int i = indexStart; i < indexEnd; i++) {
            array[i] = value;
        }
    }
    
    /* 
        Can handle the situation when the end index is more that the arrayInit, just filling others with 0
    */
    public static double[] Copy(double[] arrayInit, int indexStart, int indexEnd){
        double[] arrayResult = new double [indexEnd - indexStart];
        if(indexEnd < arrayInit.length){
            for(int i = 0; i < indexEnd - indexStart; i++) {
                arrayResult[i] = arrayInit[indexStart + i];
            }
        }
        else{
            for(int i = 0; i < arrayInit.length - indexStart; i++) {
                arrayResult[i] = arrayInit[indexStart + i];
            }
            for(int i = arrayInit.length; i < indexEnd; i++) {
                arrayResult[i] = 0;
            }
        }
        
        return arrayResult;
    }
    
    public static List<Integer> Copy(List<Integer> arrayInit, int indexStart, int indexEnd){
        List<Integer> arrayResult = new ArrayList<Integer>();
        if(indexEnd < arrayInit.size()){
            for(int i = 0; i < indexEnd - indexStart; i++) {
                arrayResult.add(arrayInit.get(indexStart + i));
            }
        }
        else{
            for(int i = 0; i < arrayInit.size() - indexStart; i++) {
                arrayResult.add(arrayInit.get(indexStart + i));
            }
            for(int i = arrayInit.size(); i < indexEnd; i++) {
                arrayResult.add(0);
            }
        }
        
        return arrayResult;
    }
    
    /* 
        Can handle the situation when the end index is more that the arrayInit, just filling others with 0
    */
    public static int[] Copy(int[] arrayInit, int indexStart, int indexEnd){
        int[] arrayResult = new int [indexEnd - indexStart];
        if(indexEnd < arrayInit.length){
            for(int i = 0; i < indexEnd - indexStart; i++) {
                arrayResult[i] = arrayInit[indexStart + i];
            }
        }
        else{
            for(int i = 0; i < arrayInit.length - indexStart; i++) {
                arrayResult[i] = arrayInit[indexStart + i];
            }
            for(int i = arrayInit.length; i < indexEnd; i++) {
                arrayResult[i] = 0;
            }
        }
        
        return arrayResult;
    }
    
    public static int SumOverArray(int[] array){
        int sum = 0;
        for (int i = 0; i < array.length; i++) {
            sum += array[i];
        }
        return sum;
    }
    
    public static double SumOverArray(double[] array){
        double sum = 0;
        for (int i = 0; i < array.length; i++) {
            sum += array[i];
        }
        return sum;
    }
    
    public static int SumOverProcessingTimesInActivitiesArray(Activity[] array){
        int sum = 0;
        for (int i = 0; i < array.length; i++) {
            sum += array[i].getProcTime();
        }
        return sum;
    }
    
    public static double[] CreateDoubleArrayFromIntArray(int[] array){
        double[] arrayDouble = new double[array.length];
        for(int i = 0; i < array.length; i++) {
            arrayDouble[i] = array[i];
        }
        return arrayDouble;
    }
    
    public static int MaxValueInArray(int[] array){
        int max = 0;
        for(int i = 0; i < array.length; i++) {
            if(max < array[i])
                max = array[i];
        }
        return max;
    }
    
    public static int MinValueInArray(int[] array){
        int min = Integer.MAX_VALUE;
        for(int i = 0; i < array.length; i++) {
            if(min > array[i])
                min = array[i];
        }
        return min;
    }
    
    public static int Get1DLengthOf2DArray(int[][] array){
        int length = 0;
        for(int i = 0; i < array.length; i++) {
            length += array[i].length;
        }
        return length;
    }
    
    public static boolean TwoArraysHaveNonEmptyIntersectionMoreThanNumber(int[] array1, int[] array2, int number){
        for(int i = 0; i < array1.length; i++) {
            for(int j = 0; j < array2.length; j++) {
                if(array1[i] == array2[j] && array1[i] >= number){
                    return true;
                }
            }
        }
        return false;
    }
    
    public static boolean TwoArraysHaveNonEmptyIntersection(int[] array1, int[] array2){
        for(int i = 0; i < array1.length; i++) {
            for(int j = 0; j < array2.length; j++) {
                if(array1[i] == array2[j]){
                    return true;
                }
            }
        }
        return false;
    }
    
    //returns arrayList with pairs of intersecting elements
     public static List<List<Integer>>IntersectionOfTwoArrays(int[] array1, int[] array2){
        List<List<Integer>> intersection = new ArrayList<List<Integer>>();
        int counterOfIntersections = 0;
        for(int i = 0; i < array1.length; i++) {
            for(int j = 0; j < array2.length; j++) {
                if(array1[i] == array2[j]){
                    intersection.add(new ArrayList<Integer>());
                    intersection.get(counterOfIntersections).add(i);
                    intersection.get(counterOfIntersections).add(j);
                    counterOfIntersections++;
                }
            }
        }
        return intersection;
    }
     
    public static boolean ArrayListContainsValue(List<Integer> array1, int value){
        for(int i = 0; i < array1.size(); i++) {
            if(array1.get(i) == value){
                return true;
            }
        }
        return false;
    } 
     
    public static boolean ArrayContainsValue(int[] array1, int value){
        for(int i = 0; i < array1.length; i++) {
            if(array1[i] == value){
                return true;
            }
        }
        return false;
    }
     
     public static List<Integer> WhichElementsHaveTheValue(int[] array, int value){
        List<Integer> elementsOfGivenValue = new ArrayList<Integer>();
        for(int i = 0; i < array.length; i++) {
            if(array[i] == value) elementsOfGivenValue.add(i);
        }
        return elementsOfGivenValue;
    }
     
     public static void SortArrayListBasedOnFirstElements(List<List<Integer>> array){
         Collections.sort(array, new Comparator<List<Integer>>() {
            @Override
            public int compare(final List<Integer> entry1, final List<Integer> entry2) {
                final int s1 = entry1.get(0);
                final int s2 = entry2.get(0);
                if(s1 - s2 != 0){
                    return s1 - s2;
                }
                else{
                    return entry1.get(1) - entry2.get(1);
                }
            }
        });
     }
     
     public static void AddNaturalNumbersToArrayList(List<Integer> array, int n){
        for(int i = 0; i < n; i++){
            array.add(i);
        }
     }
     
    public static List<Integer> CreateArrayWithNaturalNumbers(int n){
        List<Integer> array = new ArrayList<>();
        for(int i = 0; i < n; i++){
            array.add(i);
        }
        return array;
    }
     
     public static void AddNaturalNumbersToStack(Stack stack, int n){
        for(int i = n - 1; i >= 0; i--){
            stack.push(i);
        }
     }
     
     // the second dimension of the array in which to search must be equal to the dimension of the array which elements to search
     // looking for exact matches. VALUES OF THE SECOND ARRAY ARE SUBTRACTED BY 1 because input is given in a matlab form of doing 
     // arrays, from 1
     public static int GetNumberOfAppearence(List<Integer> arrayWhichElementsToSearch, List<List<Integer>> arrayInWhichToSearch){
        int numOfAppear = 0;
        for(int i = 0; i < arrayInWhichToSearch.size(); i++){
            boolean isTheSame = true;
            for(int j = 0; j < arrayWhichElementsToSearch.size(); j++) {
                if(arrayInWhichToSearch.get(i).get(j) - 1 != arrayWhichElementsToSearch.get(j)){
                    isTheSame = false;
                    break;
                }
            }
            if(isTheSame){
                numOfAppear++;
            }
        }
        return numOfAppear;
     }
     
    public static int[] ArrayListToIntArray(List<Integer> list)  {
        int[] ret = new int[list.size()];
        int i = 0;
        for (Integer e : list)  
            ret[i++] = e;
        return ret;
    }
     
    public static Activity[] ArrayListToActivityArray(List<Activity> list)  {
        Activity[] ret = new Activity[list.size()];
        int i = 0;
        for (Activity e : list)  
            ret[i++] = e;
        return ret;
    }
     
    public static int ReadIntegerNumber(Scanner in){
        String s = in.nextLine();
        String[] t = s.split(" ");
        String[] k = t[2].split(";");
        return Integer.valueOf(k[0]);
    }
    
    public static int[] ReadIntegerArray(Scanner in, int length){
        int[] array = new int[length];
        String s = in.nextLine();

        s = in.nextLine();
        String[] t = s.split("\\[");
        String[] y = t[1].split("\\,");
        
        for (int i = 0; i < array.length - 1; i++) {
          array[i] = Integer.valueOf(y[i]);
        }

        t = y[array.length - 1].split("\\]");
        array[array.length - 1] = Integer.valueOf(t[0]);
        
        return array;
    }
    
    public static int[] ReadIntegerArrayWithoutGivenLegth(Scanner in){
        List<Integer> array = new ArrayList<Integer>();
        String s = in.nextLine();

        s = in.nextLine();
        String[] t = s.split("\\[");
        String[] y = t[1].split("\\,");

        for(int j = 0; j < y.length - 1; j++) {
            array.add(Integer.valueOf(y[j]));
        }
        
        t = y[array.size() - 1].split("\\]");
        array.add(Integer.valueOf(t[0]));
        
        int[] outputArray = new int[array.size()];
        for(int i = 0; i < array.size(); i++) {
            outputArray[i] = array.get(i);
        }
        
        return outputArray;
    }
    
    public static List<List<Integer>> Read2DIntegerArray(Scanner in){
        List<List<Integer>> array = new ArrayList<List<Integer>>();
        String s = in.nextLine();

        s = in.nextLine();
        String[] t = s.split("\\[");
        String[] y;
        
        for(int i = 2; i < t.length; i++) {
            array.add(new ArrayList<Integer>());
             y = t[i].split("\\,");
            if(y[0].split("\\]").length == 0){
                continue;
            }
          
            for(int j = 0; j < y.length - 1; j++) {
                array.get(i - 2).add(Integer.valueOf(y[j]));
            }
            
            String[] temp = y[y.length - 1].split("\\]");
            if(!temp[0].isEmpty()) array.get(i - 2).add(Integer.valueOf(temp[0]));
        }

        return array;
    }
    
    public static void Initialize2dArrayWithValue(int[][] array, int value){
            for(int i = 0; i < array.length; i++) {
                for(int j = 0; j < array[i].length; j++) {
                    array[i][j] = value;
                }
            }
    }
    
    public static void PrintArrayList(List<Integer> array){
        System.out.print("\n");
        for(int i = 0; i < array.size(); i++) {
            System.out.print(array.get(i) + " ");
        }
        System.out.print("\n");
    }
    
    public static List<Integer> DifferenceOfTwoSets(List<Integer> arrayLarger, List<Integer> arraySmaller){
        for(int i = 0; i < arraySmaller.size(); i++) {
            arrayLarger.remove(arrayLarger.indexOf(arraySmaller.get(i)));
        }
        
        return arrayLarger;
    }
}
