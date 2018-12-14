class MainClass {
    def main(): int {
        writeln(new SecondMain().main());
        return 0;
    }
}

class SecondMain {
    var s : Rectangle;
    def main() : int {
        var x : int;
        #var x : int;
        y = 12;
        s = new Rectangle();
        x = s.constructor(10, 5);
        return s.area();
    }
}

class Rectangle {
    var x1 : int;
    var y1 : int;
    var name : string;
    #var z : new int[0];
    def constructor(x : int, y : int) : int {
        x1 = x;
        y1 = z.length;
        z[3] = x1;
        z[4] = (z[3] * 2 * (5 + 5));
        return 0;
    }
    def area() : int {
        return x * y;
    }
}