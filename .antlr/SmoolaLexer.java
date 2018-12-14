// Generated from c:\JavaLib\example\Phase2-provided_code\src\Smoola.g4 by ANTLR 4.7.1

        import main.ast.node.*;
        import main.ast.node.expression.*;
        import main.ast.node.declaration.*;
        import main.ast.*;
        import main.ast.Type.ArrayType.*;
        import main.ast.Type.UserDefinedType.*;
        import main.ast.Type.PrimitiveType.*;
        import main.ast.Type.*;
        import java.util.ArrayList;
        import main.ast.node.statement.*;
        import main.ast.node.expression.BinOp.BinaryOperator;
        import main.ast.node.expression.Value.*;
    
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.misc.*;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class SmoolaLexer extends Lexer {
	static { RuntimeMetaData.checkVersion("4.7.1", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		T__0=1, T__1=2, T__2=3, T__3=4, T__4=5, T__5=6, T__6=7, T__7=8, T__8=9, 
		T__9=10, T__10=11, T__11=12, T__12=13, T__13=14, T__14=15, T__15=16, T__16=17, 
		T__17=18, T__18=19, T__19=20, T__20=21, T__21=22, T__22=23, T__23=24, 
		T__24=25, T__25=26, T__26=27, T__27=28, T__28=29, T__29=30, T__30=31, 
		T__31=32, T__32=33, T__33=34, T__34=35, T__35=36, T__36=37, T__37=38, 
		T__38=39, T__39=40, T__40=41, T__41=42, CONST_NUM=43, CONST_STR=44, NL=45, 
		ID=46, COMMENT=47, WS=48;
	public static String[] channelNames = {
		"DEFAULT_TOKEN_CHANNEL", "HIDDEN"
	};

	public static String[] modeNames = {
		"DEFAULT_MODE"
	};

	public static final String[] ruleNames = {
		"T__0", "T__1", "T__2", "T__3", "T__4", "T__5", "T__6", "T__7", "T__8", 
		"T__9", "T__10", "T__11", "T__12", "T__13", "T__14", "T__15", "T__16", 
		"T__17", "T__18", "T__19", "T__20", "T__21", "T__22", "T__23", "T__24", 
		"T__25", "T__26", "T__27", "T__28", "T__29", "T__30", "T__31", "T__32", 
		"T__33", "T__34", "T__35", "T__36", "T__37", "T__38", "T__39", "T__40", 
		"T__41", "CONST_NUM", "CONST_STR", "NL", "ID", "COMMENT", "WS"
	};

	private static final String[] _LITERAL_NAMES = {
		null, "'class'", "'{'", "'def'", "'()'", "':'", "'int'", "'return'", "';'", 
		"'}'", "'extends'", "'var'", "'('", "','", "')'", "'if'", "'then'", "'else'", 
		"'while'", "'writeln('", "'='", "'||'", "'&&'", "'=='", "'<>'", "'<'", 
		"'>'", "'+'", "'-'", "'*'", "'/'", "'!'", "'['", "']'", "'.'", "'length'", 
		"'new '", "'this'", "'true'", "'false'", "'boolean'", "'string'", "'int[]'"
	};
	private static final String[] _SYMBOLIC_NAMES = {
		null, null, null, null, null, null, null, null, null, null, null, null, 
		null, null, null, null, null, null, null, null, null, null, null, null, 
		null, null, null, null, null, null, null, null, null, null, null, null, 
		null, null, null, null, null, null, null, "CONST_NUM", "CONST_STR", "NL", 
		"ID", "COMMENT", "WS"
	};
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}


	        void setPosition( Node node , int line , int col )
	        {
	            node.setLineNum( line );
	            node.setColNum( col );
	        }
	        ClassDeclaration constructObjectClass()
	        {
	            ClassDeclaration objectClass = new ClassDeclaration( new Identifier( "Object" ) , null );
	            MethodDeclaration toStringMethod = new MethodDeclaration( new Identifier( "toString" ) );
	            toStringMethod.setActualReturnType( new StringType() );
	            toStringMethod.setReturnValue( new StringValue( "Object" , new StringType() ) );
	            objectClass.addMethodDeclaration( toStringMethod );
	            return objectClass;
	        }
	    

	public SmoolaLexer(CharStream input) {
		super(input);
		_interp = new LexerATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@Override
	public String getGrammarFileName() { return "Smoola.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public String[] getChannelNames() { return channelNames; }

	@Override
	public String[] getModeNames() { return modeNames; }

	@Override
	public ATN getATN() { return _ATN; }

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2\62\u012d\b\1\4\2"+
		"\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4"+
		"\13\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22"+
		"\t\22\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30\4\31"+
		"\t\31\4\32\t\32\4\33\t\33\4\34\t\34\4\35\t\35\4\36\t\36\4\37\t\37\4 \t"+
		" \4!\t!\4\"\t\"\4#\t#\4$\t$\4%\t%\4&\t&\4\'\t\'\4(\t(\4)\t)\4*\t*\4+\t"+
		"+\4,\t,\4-\t-\4.\t.\4/\t/\4\60\t\60\4\61\t\61\3\2\3\2\3\2\3\2\3\2\3\2"+
		"\3\3\3\3\3\4\3\4\3\4\3\4\3\5\3\5\3\5\3\6\3\6\3\7\3\7\3\7\3\7\3\b\3\b\3"+
		"\b\3\b\3\b\3\b\3\b\3\t\3\t\3\n\3\n\3\13\3\13\3\13\3\13\3\13\3\13\3\13"+
		"\3\13\3\f\3\f\3\f\3\f\3\r\3\r\3\16\3\16\3\17\3\17\3\20\3\20\3\20\3\21"+
		"\3\21\3\21\3\21\3\21\3\22\3\22\3\22\3\22\3\22\3\23\3\23\3\23\3\23\3\23"+
		"\3\23\3\24\3\24\3\24\3\24\3\24\3\24\3\24\3\24\3\24\3\25\3\25\3\26\3\26"+
		"\3\26\3\27\3\27\3\27\3\30\3\30\3\30\3\31\3\31\3\31\3\32\3\32\3\33\3\33"+
		"\3\34\3\34\3\35\3\35\3\36\3\36\3\37\3\37\3 \3 \3!\3!\3\"\3\"\3#\3#\3$"+
		"\3$\3$\3$\3$\3$\3$\3%\3%\3%\3%\3%\3&\3&\3&\3&\3&\3\'\3\'\3\'\3\'\3\'\3"+
		"(\3(\3(\3(\3(\3(\3)\3)\3)\3)\3)\3)\3)\3)\3*\3*\3*\3*\3*\3*\3*\3+\3+\3"+
		"+\3+\3+\3+\3,\6,\u0106\n,\r,\16,\u0107\3-\3-\7-\u010c\n-\f-\16-\u010f"+
		"\13-\3-\3-\3.\5.\u0114\n.\3.\3.\3.\3.\3/\3/\7/\u011c\n/\f/\16/\u011f\13"+
		"/\3\60\3\60\7\60\u0123\n\60\f\60\16\60\u0126\13\60\3\60\3\60\3\61\3\61"+
		"\3\61\3\61\2\2\62\3\3\5\4\7\5\t\6\13\7\r\b\17\t\21\n\23\13\25\f\27\r\31"+
		"\16\33\17\35\20\37\21!\22#\23%\24\'\25)\26+\27-\30/\31\61\32\63\33\65"+
		"\34\67\359\36;\37= ?!A\"C#E$G%I&K\'M(O)Q*S+U,W-Y.[/]\60_\61a\62\3\2\b"+
		"\3\2\62;\5\2\f\f\17\17$$\5\2C\\aac|\6\2\62;C\\aac|\4\2\f\f\17\17\4\2\13"+
		"\13\"\"\2\u0131\2\3\3\2\2\2\2\5\3\2\2\2\2\7\3\2\2\2\2\t\3\2\2\2\2\13\3"+
		"\2\2\2\2\r\3\2\2\2\2\17\3\2\2\2\2\21\3\2\2\2\2\23\3\2\2\2\2\25\3\2\2\2"+
		"\2\27\3\2\2\2\2\31\3\2\2\2\2\33\3\2\2\2\2\35\3\2\2\2\2\37\3\2\2\2\2!\3"+
		"\2\2\2\2#\3\2\2\2\2%\3\2\2\2\2\'\3\2\2\2\2)\3\2\2\2\2+\3\2\2\2\2-\3\2"+
		"\2\2\2/\3\2\2\2\2\61\3\2\2\2\2\63\3\2\2\2\2\65\3\2\2\2\2\67\3\2\2\2\2"+
		"9\3\2\2\2\2;\3\2\2\2\2=\3\2\2\2\2?\3\2\2\2\2A\3\2\2\2\2C\3\2\2\2\2E\3"+
		"\2\2\2\2G\3\2\2\2\2I\3\2\2\2\2K\3\2\2\2\2M\3\2\2\2\2O\3\2\2\2\2Q\3\2\2"+
		"\2\2S\3\2\2\2\2U\3\2\2\2\2W\3\2\2\2\2Y\3\2\2\2\2[\3\2\2\2\2]\3\2\2\2\2"+
		"_\3\2\2\2\2a\3\2\2\2\3c\3\2\2\2\5i\3\2\2\2\7k\3\2\2\2\to\3\2\2\2\13r\3"+
		"\2\2\2\rt\3\2\2\2\17x\3\2\2\2\21\177\3\2\2\2\23\u0081\3\2\2\2\25\u0083"+
		"\3\2\2\2\27\u008b\3\2\2\2\31\u008f\3\2\2\2\33\u0091\3\2\2\2\35\u0093\3"+
		"\2\2\2\37\u0095\3\2\2\2!\u0098\3\2\2\2#\u009d\3\2\2\2%\u00a2\3\2\2\2\'"+
		"\u00a8\3\2\2\2)\u00b1\3\2\2\2+\u00b3\3\2\2\2-\u00b6\3\2\2\2/\u00b9\3\2"+
		"\2\2\61\u00bc\3\2\2\2\63\u00bf\3\2\2\2\65\u00c1\3\2\2\2\67\u00c3\3\2\2"+
		"\29\u00c5\3\2\2\2;\u00c7\3\2\2\2=\u00c9\3\2\2\2?\u00cb\3\2\2\2A\u00cd"+
		"\3\2\2\2C\u00cf\3\2\2\2E\u00d1\3\2\2\2G\u00d3\3\2\2\2I\u00da\3\2\2\2K"+
		"\u00df\3\2\2\2M\u00e4\3\2\2\2O\u00e9\3\2\2\2Q\u00ef\3\2\2\2S\u00f7\3\2"+
		"\2\2U\u00fe\3\2\2\2W\u0105\3\2\2\2Y\u0109\3\2\2\2[\u0113\3\2\2\2]\u0119"+
		"\3\2\2\2_\u0120\3\2\2\2a\u0129\3\2\2\2cd\7e\2\2de\7n\2\2ef\7c\2\2fg\7"+
		"u\2\2gh\7u\2\2h\4\3\2\2\2ij\7}\2\2j\6\3\2\2\2kl\7f\2\2lm\7g\2\2mn\7h\2"+
		"\2n\b\3\2\2\2op\7*\2\2pq\7+\2\2q\n\3\2\2\2rs\7<\2\2s\f\3\2\2\2tu\7k\2"+
		"\2uv\7p\2\2vw\7v\2\2w\16\3\2\2\2xy\7t\2\2yz\7g\2\2z{\7v\2\2{|\7w\2\2|"+
		"}\7t\2\2}~\7p\2\2~\20\3\2\2\2\177\u0080\7=\2\2\u0080\22\3\2\2\2\u0081"+
		"\u0082\7\177\2\2\u0082\24\3\2\2\2\u0083\u0084\7g\2\2\u0084\u0085\7z\2"+
		"\2\u0085\u0086\7v\2\2\u0086\u0087\7g\2\2\u0087\u0088\7p\2\2\u0088\u0089"+
		"\7f\2\2\u0089\u008a\7u\2\2\u008a\26\3\2\2\2\u008b\u008c\7x\2\2\u008c\u008d"+
		"\7c\2\2\u008d\u008e\7t\2\2\u008e\30\3\2\2\2\u008f\u0090\7*\2\2\u0090\32"+
		"\3\2\2\2\u0091\u0092\7.\2\2\u0092\34\3\2\2\2\u0093\u0094\7+\2\2\u0094"+
		"\36\3\2\2\2\u0095\u0096\7k\2\2\u0096\u0097\7h\2\2\u0097 \3\2\2\2\u0098"+
		"\u0099\7v\2\2\u0099\u009a\7j\2\2\u009a\u009b\7g\2\2\u009b\u009c\7p\2\2"+
		"\u009c\"\3\2\2\2\u009d\u009e\7g\2\2\u009e\u009f\7n\2\2\u009f\u00a0\7u"+
		"\2\2\u00a0\u00a1\7g\2\2\u00a1$\3\2\2\2\u00a2\u00a3\7y\2\2\u00a3\u00a4"+
		"\7j\2\2\u00a4\u00a5\7k\2\2\u00a5\u00a6\7n\2\2\u00a6\u00a7\7g\2\2\u00a7"+
		"&\3\2\2\2\u00a8\u00a9\7y\2\2\u00a9\u00aa\7t\2\2\u00aa\u00ab\7k\2\2\u00ab"+
		"\u00ac\7v\2\2\u00ac\u00ad\7g\2\2\u00ad\u00ae\7n\2\2\u00ae\u00af\7p\2\2"+
		"\u00af\u00b0\7*\2\2\u00b0(\3\2\2\2\u00b1\u00b2\7?\2\2\u00b2*\3\2\2\2\u00b3"+
		"\u00b4\7~\2\2\u00b4\u00b5\7~\2\2\u00b5,\3\2\2\2\u00b6\u00b7\7(\2\2\u00b7"+
		"\u00b8\7(\2\2\u00b8.\3\2\2\2\u00b9\u00ba\7?\2\2\u00ba\u00bb\7?\2\2\u00bb"+
		"\60\3\2\2\2\u00bc\u00bd\7>\2\2\u00bd\u00be\7@\2\2\u00be\62\3\2\2\2\u00bf"+
		"\u00c0\7>\2\2\u00c0\64\3\2\2\2\u00c1\u00c2\7@\2\2\u00c2\66\3\2\2\2\u00c3"+
		"\u00c4\7-\2\2\u00c48\3\2\2\2\u00c5\u00c6\7/\2\2\u00c6:\3\2\2\2\u00c7\u00c8"+
		"\7,\2\2\u00c8<\3\2\2\2\u00c9\u00ca\7\61\2\2\u00ca>\3\2\2\2\u00cb\u00cc"+
		"\7#\2\2\u00cc@\3\2\2\2\u00cd\u00ce\7]\2\2\u00ceB\3\2\2\2\u00cf\u00d0\7"+
		"_\2\2\u00d0D\3\2\2\2\u00d1\u00d2\7\60\2\2\u00d2F\3\2\2\2\u00d3\u00d4\7"+
		"n\2\2\u00d4\u00d5\7g\2\2\u00d5\u00d6\7p\2\2\u00d6\u00d7\7i\2\2\u00d7\u00d8"+
		"\7v\2\2\u00d8\u00d9\7j\2\2\u00d9H\3\2\2\2\u00da\u00db\7p\2\2\u00db\u00dc"+
		"\7g\2\2\u00dc\u00dd\7y\2\2\u00dd\u00de\7\"\2\2\u00deJ\3\2\2\2\u00df\u00e0"+
		"\7v\2\2\u00e0\u00e1\7j\2\2\u00e1\u00e2\7k\2\2\u00e2\u00e3\7u\2\2\u00e3"+
		"L\3\2\2\2\u00e4\u00e5\7v\2\2\u00e5\u00e6\7t\2\2\u00e6\u00e7\7w\2\2\u00e7"+
		"\u00e8\7g\2\2\u00e8N\3\2\2\2\u00e9\u00ea\7h\2\2\u00ea\u00eb\7c\2\2\u00eb"+
		"\u00ec\7n\2\2\u00ec\u00ed\7u\2\2\u00ed\u00ee\7g\2\2\u00eeP\3\2\2\2\u00ef"+
		"\u00f0\7d\2\2\u00f0\u00f1\7q\2\2\u00f1\u00f2\7q\2\2\u00f2\u00f3\7n\2\2"+
		"\u00f3\u00f4\7g\2\2\u00f4\u00f5\7c\2\2\u00f5\u00f6\7p\2\2\u00f6R\3\2\2"+
		"\2\u00f7\u00f8\7u\2\2\u00f8\u00f9\7v\2\2\u00f9\u00fa\7t\2\2\u00fa\u00fb"+
		"\7k\2\2\u00fb\u00fc\7p\2\2\u00fc\u00fd\7i\2\2\u00fdT\3\2\2\2\u00fe\u00ff"+
		"\7k\2\2\u00ff\u0100\7p\2\2\u0100\u0101\7v\2\2\u0101\u0102\7]\2\2\u0102"+
		"\u0103\7_\2\2\u0103V\3\2\2\2\u0104\u0106\t\2\2\2\u0105\u0104\3\2\2\2\u0106"+
		"\u0107\3\2\2\2\u0107\u0105\3\2\2\2\u0107\u0108\3\2\2\2\u0108X\3\2\2\2"+
		"\u0109\u010d\7$\2\2\u010a\u010c\n\3\2\2\u010b\u010a\3\2\2\2\u010c\u010f"+
		"\3\2\2\2\u010d\u010b\3\2\2\2\u010d\u010e\3\2\2\2\u010e\u0110\3\2\2\2\u010f"+
		"\u010d\3\2\2\2\u0110\u0111\7$\2\2\u0111Z\3\2\2\2\u0112\u0114\7\17\2\2"+
		"\u0113\u0112\3\2\2\2\u0113\u0114\3\2\2\2\u0114\u0115\3\2\2\2\u0115\u0116"+
		"\7\f\2\2\u0116\u0117\3\2\2\2\u0117\u0118\b.\2\2\u0118\\\3\2\2\2\u0119"+
		"\u011d\t\4\2\2\u011a\u011c\t\5\2\2\u011b\u011a\3\2\2\2\u011c\u011f\3\2"+
		"\2\2\u011d\u011b\3\2\2\2\u011d\u011e\3\2\2\2\u011e^\3\2\2\2\u011f\u011d"+
		"\3\2\2\2\u0120\u0124\7%\2\2\u0121\u0123\n\6\2\2\u0122\u0121\3\2\2\2\u0123"+
		"\u0126\3\2\2\2\u0124\u0122\3\2\2\2\u0124\u0125\3\2\2\2\u0125\u0127\3\2"+
		"\2\2\u0126\u0124\3\2\2\2\u0127\u0128\b\60\2\2\u0128`\3\2\2\2\u0129\u012a"+
		"\t\7\2\2\u012a\u012b\3\2\2\2\u012b\u012c\b\61\2\2\u012cb\3\2\2\2\b\2\u0107"+
		"\u010d\u0113\u011d\u0124\3\b\2\2";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}