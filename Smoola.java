import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;

import java.io.IOException;

public class Smoola {
    public static void main( String[] args )
    {
        try {
            CharStream reader = CharStreams.fromFileName(args[0]);
            SmoolaCompiler compiler = new SmoolaCompiler();
            compiler.compile( reader );
        }
        catch( IOException noSuchFileFound )
        {
            System.out.println( "there is no file with name " + args[ 0 ] );
        }
    }
}
