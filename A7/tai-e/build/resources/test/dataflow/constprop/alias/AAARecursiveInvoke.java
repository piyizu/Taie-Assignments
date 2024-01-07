public class AAARecursiveInvoke {
    static void main(String args[]) {
        int a = fun(1);
        return;
    }

    static int fun(int x) {
        if(x > 0) return x * fun(x);
        else return 1;
    }

}