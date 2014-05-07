class ReverseOverflow {

    public static void main(String[] args) {
	foo(new int[2]);
    }

    public static void foo(int[] arr) {
	for (int i = arr.length - 1; i >= 0; i++) {
	    arr[i] = 7;
	}
    }

}