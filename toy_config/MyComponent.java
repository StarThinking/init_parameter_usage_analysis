import org.apache.hadoop.conf.Configuration;

public class MyComponent {

    public MyComponent(Configuration conf) {
        System.out.println("MyComponent is to be initialized.");
    }

    public static void main(String[] args) {
        Configuration conf = new Configuration();
        MyComponent component = new MyComponent(conf);
    }
}
