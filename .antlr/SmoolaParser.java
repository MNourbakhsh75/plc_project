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
    
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class SmoolaParser extends Parser {
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
	public static final int
		RULE_program = 0, RULE_mainClass = 1, RULE_classDeclaration = 2, RULE_varDeclaration = 3, 
		RULE_methodDeclaration = 4, RULE_statements = 5, RULE_statement = 6, RULE_statementBlock = 7, 
		RULE_statementCondition = 8, RULE_statementLoop = 9, RULE_statementWrite = 10, 
		RULE_statementAssignment = 11, RULE_expression = 12, RULE_expressionAssignment = 13, 
		RULE_expressionOr = 14, RULE_expressionOrTemp = 15, RULE_expressionAnd = 16, 
		RULE_expressionAndTemp = 17, RULE_expressionEq = 18, RULE_expressionEqTemp = 19, 
		RULE_expressionCmp = 20, RULE_expressionCmpTemp = 21, RULE_expressionAdd = 22, 
		RULE_expressionAddTemp = 23, RULE_expressionMult = 24, RULE_expressionMultTemp = 25, 
		RULE_expressionUnary = 26, RULE_expressionMem = 27, RULE_expressionMemTemp = 28, 
		RULE_expressionMethods = 29, RULE_expressionMethodsTemp = 30, RULE_expressionOther = 31, 
		RULE_type = 32;
	public static final String[] ruleNames = {
		"program", "mainClass", "classDeclaration", "varDeclaration", "methodDeclaration", 
		"statements", "statement", "statementBlock", "statementCondition", "statementLoop", 
		"statementWrite", "statementAssignment", "expression", "expressionAssignment", 
		"expressionOr", "expressionOrTemp", "expressionAnd", "expressionAndTemp", 
		"expressionEq", "expressionEqTemp", "expressionCmp", "expressionCmpTemp", 
		"expressionAdd", "expressionAddTemp", "expressionMult", "expressionMultTemp", 
		"expressionUnary", "expressionMem", "expressionMemTemp", "expressionMethods", 
		"expressionMethodsTemp", "expressionOther", "type"
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

	@Override
	public String getGrammarFileName() { return "Smoola.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public ATN getATN() { return _ATN; }


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
	    
	public SmoolaParser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}
	public static class ProgramContext extends ParserRuleContext {
		public Program returnedProgram;
		public Program myProgram;
		public MainClassContext myClass;
		public ClassDeclarationContext otherClass;
		public TerminalNode EOF() { return getToken(SmoolaParser.EOF, 0); }
		public MainClassContext mainClass() {
			return getRuleContext(MainClassContext.class,0);
		}
		public List<ClassDeclarationContext> classDeclaration() {
			return getRuleContexts(ClassDeclarationContext.class);
		}
		public ClassDeclarationContext classDeclaration(int i) {
			return getRuleContext(ClassDeclarationContext.class,i);
		}
		public ProgramContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_program; }
	}

	public final ProgramContext program() throws RecognitionException {
		ProgramContext _localctx = new ProgramContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_program);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{

			            ((ProgramContext)_localctx).myProgram =  new Program();
			        
			setState(67);
			((ProgramContext)_localctx).myClass = mainClass();

			            _localctx.myProgram.setMainClass( ((ProgramContext)_localctx).myClass.mainClassDeclaration );
			        
			setState(74);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__0) {
				{
				{
				setState(69);
				((ProgramContext)_localctx).otherClass = classDeclaration();

				            _localctx.myProgram.addClass( ((ProgramContext)_localctx).otherClass.myClassDeclaration );
				        
				}
				}
				setState(76);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(77);
			match(EOF);

			            ClassDeclaration objectClass = constructObjectClass();
			            ((ProgramContext)_localctx).returnedProgram =  _localctx.myProgram;
			        
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class MainClassContext extends ParserRuleContext {
		public ClassDeclaration mainClassDeclaration;
		public MethodDeclaration mainMethodDec;
		public Token className;
		public Token mainMethod;
		public StatementsContext stats;
		public ExpressionContext retExpr;
		public List<TerminalNode> ID() { return getTokens(SmoolaParser.ID); }
		public TerminalNode ID(int i) {
			return getToken(SmoolaParser.ID, i);
		}
		public StatementsContext statements() {
			return getRuleContext(StatementsContext.class,0);
		}
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public MainClassContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_mainClass; }
	}

	public final MainClassContext mainClass() throws RecognitionException {
		MainClassContext _localctx = new MainClassContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_mainClass);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(80);
			match(T__0);
			setState(81);
			((MainClassContext)_localctx).className = match(ID);

			            ((MainClassContext)_localctx).mainClassDeclaration =  new ClassDeclaration( new Identifier( (((MainClassContext)_localctx).className!=null?((MainClassContext)_localctx).className.getText():null) ) , null );
			            setPosition( _localctx.mainClassDeclaration.getName() , ((MainClassContext)_localctx).className.getLine() , ((MainClassContext)_localctx).className.getCharPositionInLine() );

			        
			setState(83);
			match(T__1);
			setState(84);
			match(T__2);
			setState(85);
			((MainClassContext)_localctx).mainMethod = match(ID);
			setState(86);
			match(T__3);
			setState(87);
			match(T__4);
			setState(88);
			match(T__5);

			            ((MainClassContext)_localctx).mainMethodDec =  new MainMethodDeclaration( new Identifier( (((MainClassContext)_localctx).mainMethod!=null?((MainClassContext)_localctx).mainMethod.getText():null) ) ) ;
			            _localctx.mainMethodDec.setActualReturnType( new IntType() );
			            setPosition( _localctx.mainMethodDec.getName() , ((MainClassContext)_localctx).mainMethod.getLine() , ((MainClassContext)_localctx).mainMethod.getCharPositionInLine() );
			        
			setState(90);
			match(T__1);
			setState(91);
			((MainClassContext)_localctx).stats = statements();
			setState(92);
			match(T__6);
			setState(93);
			((MainClassContext)_localctx).retExpr = expression();
			setState(94);
			match(T__7);
			setState(95);
			match(T__8);
			setState(96);
			match(T__8);

			            _localctx.mainMethodDec.setReturnValue( ((MainClassContext)_localctx).retExpr.finalExpr );
			            for( Statement stat: ((MainClassContext)_localctx).stats.myStatements )
			            {
			               _localctx.mainMethodDec.addStatement( stat );
			            }
			            _localctx.mainClassDeclaration.addMethodDeclaration( _localctx.mainMethodDec );
			        
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ClassDeclarationContext extends ParserRuleContext {
		public ClassDeclaration myClassDeclaration;
		public Token className;
		public Token parentClassName;
		public VarDeclarationContext curVarDec;
		public MethodDeclarationContext methodDec;
		public List<TerminalNode> ID() { return getTokens(SmoolaParser.ID); }
		public TerminalNode ID(int i) {
			return getToken(SmoolaParser.ID, i);
		}
		public List<VarDeclarationContext> varDeclaration() {
			return getRuleContexts(VarDeclarationContext.class);
		}
		public VarDeclarationContext varDeclaration(int i) {
			return getRuleContext(VarDeclarationContext.class,i);
		}
		public List<MethodDeclarationContext> methodDeclaration() {
			return getRuleContexts(MethodDeclarationContext.class);
		}
		public MethodDeclarationContext methodDeclaration(int i) {
			return getRuleContext(MethodDeclarationContext.class,i);
		}
		public ClassDeclarationContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_classDeclaration; }
	}

	public final ClassDeclarationContext classDeclaration() throws RecognitionException {
		ClassDeclarationContext _localctx = new ClassDeclarationContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_classDeclaration);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(99);
			match(T__0);
			setState(100);
			((ClassDeclarationContext)_localctx).className = match(ID);

			            ((ClassDeclarationContext)_localctx).myClassDeclaration =  new ClassDeclaration( new Identifier( (((ClassDeclarationContext)_localctx).className!=null?((ClassDeclarationContext)_localctx).className.getText():null) ) , null );
			            setPosition( _localctx.myClassDeclaration.getName() , ((ClassDeclarationContext)_localctx).className.getLine() , ((ClassDeclarationContext)_localctx).className.getCharPositionInLine() );

			        
			setState(105);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__9) {
				{
				setState(102);
				match(T__9);
				setState(103);
				((ClassDeclarationContext)_localctx).parentClassName = match(ID);

				            _localctx.myClassDeclaration.setParentName( new Identifier( (((ClassDeclarationContext)_localctx).parentClassName!=null?((ClassDeclarationContext)_localctx).parentClassName.getText():null) ) );
				            setPosition( _localctx.myClassDeclaration.getParentName() , ((ClassDeclarationContext)_localctx).parentClassName.getLine() , ((ClassDeclarationContext)_localctx).parentClassName.getCharPositionInLine() );
				        
				}
			}

			setState(107);
			match(T__1);
			setState(113);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__10) {
				{
				{
				setState(108);
				((ClassDeclarationContext)_localctx).curVarDec = varDeclaration();

				                _localctx.myClassDeclaration.addVarDeclaration( ((ClassDeclarationContext)_localctx).curVarDec.returnedVarDeclaration );
				            
				}
				}
				setState(115);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(121);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__2) {
				{
				{
				setState(116);
				((ClassDeclarationContext)_localctx).methodDec = methodDeclaration();

				            _localctx.myClassDeclaration.addMethodDeclaration( ((ClassDeclarationContext)_localctx).methodDec.methodDec );
				        
				}
				}
				setState(123);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(124);
			match(T__8);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class VarDeclarationContext extends ParserRuleContext {
		public VarDeclaration returnedVarDeclaration;
		public Token varName;
		public TypeContext returnedType;
		public TerminalNode ID() { return getToken(SmoolaParser.ID, 0); }
		public TypeContext type() {
			return getRuleContext(TypeContext.class,0);
		}
		public VarDeclarationContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_varDeclaration; }
	}

	public final VarDeclarationContext varDeclaration() throws RecognitionException {
		VarDeclarationContext _localctx = new VarDeclarationContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_varDeclaration);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(126);
			match(T__10);
			setState(127);
			((VarDeclarationContext)_localctx).varName = match(ID);
			setState(128);
			match(T__4);
			setState(129);
			((VarDeclarationContext)_localctx).returnedType = type();
			setState(130);
			match(T__7);

			            ((VarDeclarationContext)_localctx).returnedVarDeclaration =  new VarDeclaration( new Identifier( (((VarDeclarationContext)_localctx).varName!=null?((VarDeclarationContext)_localctx).varName.getText():null) ) , ((VarDeclarationContext)_localctx).returnedType.returnedType );
			            setPosition( _localctx.returnedVarDeclaration.getIdentifier() , ((VarDeclarationContext)_localctx).varName.getLine() , ((VarDeclarationContext)_localctx).varName.getCharPositionInLine() );
			        
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class MethodDeclarationContext extends ParserRuleContext {
		public MethodDeclaration methodDec;
		public VarDeclaration argDec;
		public Token methodName;
		public Token firstArgName;
		public TypeContext firstArgType;
		public Token otherArgName;
		public TypeContext otherArgType;
		public TypeContext actualReturnType;
		public VarDeclarationContext localVar;
		public StatementsContext stats;
		public ExpressionContext retExpr;
		public List<TerminalNode> ID() { return getTokens(SmoolaParser.ID); }
		public TerminalNode ID(int i) {
			return getToken(SmoolaParser.ID, i);
		}
		public List<TypeContext> type() {
			return getRuleContexts(TypeContext.class);
		}
		public TypeContext type(int i) {
			return getRuleContext(TypeContext.class,i);
		}
		public StatementsContext statements() {
			return getRuleContext(StatementsContext.class,0);
		}
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public List<VarDeclarationContext> varDeclaration() {
			return getRuleContexts(VarDeclarationContext.class);
		}
		public VarDeclarationContext varDeclaration(int i) {
			return getRuleContext(VarDeclarationContext.class,i);
		}
		public MethodDeclarationContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_methodDeclaration; }
	}

	public final MethodDeclarationContext methodDeclaration() throws RecognitionException {
		MethodDeclarationContext _localctx = new MethodDeclarationContext(_ctx, getState());
		enterRule(_localctx, 8, RULE_methodDeclaration);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(133);
			match(T__2);
			setState(134);
			((MethodDeclarationContext)_localctx).methodName = match(ID);

			            ((MethodDeclarationContext)_localctx).methodDec =  new MethodDeclaration( new Identifier( (((MethodDeclarationContext)_localctx).methodName!=null?((MethodDeclarationContext)_localctx).methodName.getText():null) ) );
			            setPosition( _localctx.methodDec.getName() , ((MethodDeclarationContext)_localctx).methodName.getLine() , ((MethodDeclarationContext)_localctx).methodName.getCharPositionInLine() );
			        
			setState(155);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__3:
				{
				setState(136);
				match(T__3);
				}
				break;
			case T__11:
				{
				{
				setState(137);
				match(T__11);
				setState(138);
				((MethodDeclarationContext)_localctx).firstArgName = match(ID);
				setState(139);
				match(T__4);
				setState(140);
				((MethodDeclarationContext)_localctx).firstArgType = type();

				            ((MethodDeclarationContext)_localctx).argDec =  new VarDeclaration( new Identifier( (((MethodDeclarationContext)_localctx).firstArgName!=null?((MethodDeclarationContext)_localctx).firstArgName.getText():null) ) , ((MethodDeclarationContext)_localctx).firstArgType.returnedType );
				            setPosition( _localctx.argDec.getIdentifier() , ((MethodDeclarationContext)_localctx).firstArgName.getLine() , ((MethodDeclarationContext)_localctx).firstArgName.getCharPositionInLine() );
				            _localctx.methodDec.addArg( _localctx.argDec );
				        
				setState(150);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__12) {
					{
					{
					setState(142);
					match(T__12);
					setState(143);
					((MethodDeclarationContext)_localctx).otherArgName = match(ID);
					setState(144);
					match(T__4);
					setState(145);
					((MethodDeclarationContext)_localctx).otherArgType = type();

					            ((MethodDeclarationContext)_localctx).argDec =  new VarDeclaration( new Identifier( (((MethodDeclarationContext)_localctx).otherArgName!=null?((MethodDeclarationContext)_localctx).otherArgName.getText():null) ) , ((MethodDeclarationContext)_localctx).otherArgType.returnedType );
					            setPosition( _localctx.argDec.getIdentifier() , ((MethodDeclarationContext)_localctx).otherArgName.getLine() , ((MethodDeclarationContext)_localctx).otherArgName.getCharPositionInLine() );
					            _localctx.methodDec.addArg( _localctx.argDec );
					        
					}
					}
					setState(152);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				setState(153);
				match(T__13);
				}
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
			setState(157);
			match(T__4);
			setState(158);
			((MethodDeclarationContext)_localctx).actualReturnType = type();

			            _localctx.methodDec.setActualReturnType( ((MethodDeclarationContext)_localctx).actualReturnType.returnedType );
			        
			setState(160);
			match(T__1);
			setState(166);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__10) {
				{
				{
				setState(161);
				((MethodDeclarationContext)_localctx).localVar = varDeclaration();

				                    _localctx.methodDec.addLocalVar( ((MethodDeclarationContext)_localctx).localVar.returnedVarDeclaration );
				                
				}
				}
				setState(168);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(169);
			((MethodDeclarationContext)_localctx).stats = statements();
			setState(170);
			match(T__6);
			setState(171);
			((MethodDeclarationContext)_localctx).retExpr = expression();
			setState(172);
			match(T__7);
			setState(173);
			match(T__8);

			                _localctx.methodDec.setReturnValue( ((MethodDeclarationContext)_localctx).retExpr.finalExpr );
			                for( Statement stat: ((MethodDeclarationContext)_localctx).stats.myStatements )
			                {
			                    _localctx.methodDec.addStatement( stat );
			                }
			            
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class StatementsContext extends ParserRuleContext {
		public ArrayList<Statement> myStatements;
		public StatementContext stat;
		public List<StatementContext> statement() {
			return getRuleContexts(StatementContext.class);
		}
		public StatementContext statement(int i) {
			return getRuleContext(StatementContext.class,i);
		}
		public StatementsContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_statements; }
	}

	public final StatementsContext statements() throws RecognitionException {
		StatementsContext _localctx = new StatementsContext(_ctx, getState());
		enterRule(_localctx, 10, RULE_statements);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{

			             ((StatementsContext)_localctx).myStatements =  new ArrayList<>();
			        
			setState(182);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__1) | (1L << T__11) | (1L << T__14) | (1L << T__17) | (1L << T__18) | (1L << T__27) | (1L << T__30) | (1L << T__35) | (1L << T__36) | (1L << T__37) | (1L << T__38) | (1L << CONST_NUM) | (1L << CONST_STR) | (1L << ID))) != 0)) {
				{
				{
				setState(177);
				((StatementsContext)_localctx).stat = statement();

				                if( ((StatementsContext)_localctx).stat.myStatement != null ){
				                    _localctx.myStatements.add( ((StatementsContext)_localctx).stat.myStatement );
				                }
				            
				}
				}
				setState(184);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class StatementContext extends ParserRuleContext {
		public Statement myStatement;
		public StatementBlockContext seenBlock;
		public StatementConditionContext conditionalStat;
		public StatementLoopContext whileStat;
		public StatementWriteContext writeStat;
		public StatementAssignmentContext assignStat;
		public StatementBlockContext statementBlock() {
			return getRuleContext(StatementBlockContext.class,0);
		}
		public StatementConditionContext statementCondition() {
			return getRuleContext(StatementConditionContext.class,0);
		}
		public StatementLoopContext statementLoop() {
			return getRuleContext(StatementLoopContext.class,0);
		}
		public StatementWriteContext statementWrite() {
			return getRuleContext(StatementWriteContext.class,0);
		}
		public StatementAssignmentContext statementAssignment() {
			return getRuleContext(StatementAssignmentContext.class,0);
		}
		public StatementContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_statement; }
	}

	public final StatementContext statement() throws RecognitionException {
		StatementContext _localctx = new StatementContext(_ctx, getState());
		enterRule(_localctx, 12, RULE_statement);
		try {
			setState(200);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__1:
				enterOuterAlt(_localctx, 1);
				{
				setState(185);
				((StatementContext)_localctx).seenBlock = statementBlock();

				            ((StatementContext)_localctx).myStatement =  ((StatementContext)_localctx).seenBlock.block;
				        
				}
				break;
			case T__14:
				enterOuterAlt(_localctx, 2);
				{
				setState(188);
				((StatementContext)_localctx).conditionalStat = statementCondition();

				            ((StatementContext)_localctx).myStatement =  ((StatementContext)_localctx).conditionalStat.conditionStat;
				        
				}
				break;
			case T__17:
				enterOuterAlt(_localctx, 3);
				{
				setState(191);
				((StatementContext)_localctx).whileStat = statementLoop();

				            ((StatementContext)_localctx).myStatement =  ((StatementContext)_localctx).whileStat.whileStat;
				        
				}
				break;
			case T__18:
				enterOuterAlt(_localctx, 4);
				{
				setState(194);
				((StatementContext)_localctx).writeStat = statementWrite();

				            ((StatementContext)_localctx).myStatement =  ((StatementContext)_localctx).writeStat.writeStat;
				        
				}
				break;
			case T__11:
			case T__27:
			case T__30:
			case T__35:
			case T__36:
			case T__37:
			case T__38:
			case CONST_NUM:
			case CONST_STR:
			case ID:
				enterOuterAlt(_localctx, 5);
				{
				setState(197);
				((StatementContext)_localctx).assignStat = statementAssignment();

				            ((StatementContext)_localctx).myStatement =  ((StatementContext)_localctx).assignStat.assignStat;
				        
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class StatementBlockContext extends ParserRuleContext {
		public Block block;
		public StatementsContext blockStatements;
		public StatementsContext statements() {
			return getRuleContext(StatementsContext.class,0);
		}
		public StatementBlockContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_statementBlock; }
	}

	public final StatementBlockContext statementBlock() throws RecognitionException {
		StatementBlockContext _localctx = new StatementBlockContext(_ctx, getState());
		enterRule(_localctx, 14, RULE_statementBlock);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(202);
			match(T__1);
			setState(203);
			((StatementBlockContext)_localctx).blockStatements = statements();
			setState(204);
			match(T__8);

			            ((StatementBlockContext)_localctx).block =  new Block();
			            for( Statement myStatement: ((StatementBlockContext)_localctx).blockStatements.myStatements )
			                _localctx.block.addStatement( myStatement );
			        
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class StatementConditionContext extends ParserRuleContext {
		public Conditional conditionStat;
		public ExpressionContext condition;
		public StatementContext consequenceStat;
		public StatementContext altStat;
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public List<StatementContext> statement() {
			return getRuleContexts(StatementContext.class);
		}
		public StatementContext statement(int i) {
			return getRuleContext(StatementContext.class,i);
		}
		public StatementConditionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_statementCondition; }
	}

	public final StatementConditionContext statementCondition() throws RecognitionException {
		StatementConditionContext _localctx = new StatementConditionContext(_ctx, getState());
		enterRule(_localctx, 16, RULE_statementCondition);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(207);
			match(T__14);
			setState(208);
			match(T__11);
			setState(209);
			((StatementConditionContext)_localctx).condition = expression();
			setState(210);
			match(T__13);
			setState(211);
			match(T__15);
			setState(212);
			((StatementConditionContext)_localctx).consequenceStat = statement();

			            ((StatementConditionContext)_localctx).conditionStat =  new Conditional( ((StatementConditionContext)_localctx).condition.finalExpr , ((StatementConditionContext)_localctx).consequenceStat.myStatement );
			        
			setState(218);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,9,_ctx) ) {
			case 1:
				{
				setState(214);
				match(T__16);
				setState(215);
				((StatementConditionContext)_localctx).altStat = statement();

				              _localctx.conditionStat.setAlternativeBody( ((StatementConditionContext)_localctx).altStat.myStatement );
				           
				}
				break;
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class StatementLoopContext extends ParserRuleContext {
		public While whileStat;
		public ExpressionContext loopCondition;
		public StatementContext stat;
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public StatementContext statement() {
			return getRuleContext(StatementContext.class,0);
		}
		public StatementLoopContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_statementLoop; }
	}

	public final StatementLoopContext statementLoop() throws RecognitionException {
		StatementLoopContext _localctx = new StatementLoopContext(_ctx, getState());
		enterRule(_localctx, 18, RULE_statementLoop);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(220);
			match(T__17);
			setState(221);
			match(T__11);
			setState(222);
			((StatementLoopContext)_localctx).loopCondition = expression();
			setState(223);
			match(T__13);
			setState(224);
			((StatementLoopContext)_localctx).stat = statement();

			            ((StatementLoopContext)_localctx).whileStat =  new While( ((StatementLoopContext)_localctx).loopCondition.finalExpr , ((StatementLoopContext)_localctx).stat.myStatement );
			        
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class StatementWriteContext extends ParserRuleContext {
		public Write writeStat;
		public Token Id1;
		public ExpressionContext writeExpr;
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public StatementWriteContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_statementWrite; }
	}

	public final StatementWriteContext statementWrite() throws RecognitionException {
		StatementWriteContext _localctx = new StatementWriteContext(_ctx, getState());
		enterRule(_localctx, 20, RULE_statementWrite);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(227);
			((StatementWriteContext)_localctx).Id1 = match(T__18);
			setState(228);
			((StatementWriteContext)_localctx).writeExpr = expression();
			setState(229);
			match(T__13);
			setState(230);
			match(T__7);

			            ((StatementWriteContext)_localctx).writeStat =  new Write( ((StatementWriteContext)_localctx).writeExpr.finalExpr );
			            _localctx.writeStat.setLineNum(((StatementWriteContext)_localctx).Id1.getLine());

			        
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class StatementAssignmentContext extends ParserRuleContext {
		public Assign assignStat;
		public ExpressionContext expr;
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public StatementAssignmentContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_statementAssignment; }
	}

	public final StatementAssignmentContext statementAssignment() throws RecognitionException {
		StatementAssignmentContext _localctx = new StatementAssignmentContext(_ctx, getState());
		enterRule(_localctx, 22, RULE_statementAssignment);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(233);
			((StatementAssignmentContext)_localctx).expr = expression();
			setState(234);
			match(T__7);

			            ((StatementAssignmentContext)_localctx).assignStat =  new Assign( null , null );
			            if( ((StatementAssignmentContext)_localctx).expr.finalExpr instanceof BinaryExpression && ( ( BinaryExpression ) ((StatementAssignmentContext)_localctx).expr.finalExpr).getBinaryOperator().equals( BinaryOperator.assign )  )
			            {
			                BinaryExpression bExpr = ( BinaryExpression ) ((StatementAssignmentContext)_localctx).expr.finalExpr;
			                _localctx.assignStat.setrValue( bExpr.getRight() );
			                _localctx.assignStat.setlValue( bExpr.getLeft() );
			            }
			            else
			            {
			                _localctx.assignStat.setlValue( ((StatementAssignmentContext)_localctx).expr.finalExpr );
			                _localctx.assignStat.setrValue( null );
			            }
			            setPosition( _localctx.assignStat , ((StatementAssignmentContext)_localctx).expr.finalExpr.getLineNum() , ((StatementAssignmentContext)_localctx).expr.finalExpr.getColNum() );
			        
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ExpressionContext extends ParserRuleContext {
		public Expression finalExpr;
		public ExpressionAssignmentContext exprAssign;
		public ExpressionAssignmentContext expressionAssignment() {
			return getRuleContext(ExpressionAssignmentContext.class,0);
		}
		public ExpressionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_expression; }
	}

	public final ExpressionContext expression() throws RecognitionException {
		ExpressionContext _localctx = new ExpressionContext(_ctx, getState());
		enterRule(_localctx, 24, RULE_expression);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(237);
			((ExpressionContext)_localctx).exprAssign = expressionAssignment();

					    ((ExpressionContext)_localctx).finalExpr =  ((ExpressionContext)_localctx).exprAssign.assignRetExpr;
					
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ExpressionAssignmentContext extends ParserRuleContext {
		public Expression assignRetExpr;
		public ExpressionOrContext lOrExpr;
		public Token assign;
		public ExpressionAssignmentContext rAssignExpr;
		public ExpressionOrContext singleOrExpr;
		public ExpressionOrContext expressionOr() {
			return getRuleContext(ExpressionOrContext.class,0);
		}
		public ExpressionAssignmentContext expressionAssignment() {
			return getRuleContext(ExpressionAssignmentContext.class,0);
		}
		public ExpressionAssignmentContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_expressionAssignment; }
	}

	public final ExpressionAssignmentContext expressionAssignment() throws RecognitionException {
		ExpressionAssignmentContext _localctx = new ExpressionAssignmentContext(_ctx, getState());
		enterRule(_localctx, 26, RULE_expressionAssignment);
		try {
			setState(248);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,10,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(240);
				((ExpressionAssignmentContext)_localctx).lOrExpr = expressionOr();
				setState(241);
				((ExpressionAssignmentContext)_localctx).assign = match(T__19);
				setState(242);
				((ExpressionAssignmentContext)_localctx).rAssignExpr = expressionAssignment();

						    ((ExpressionAssignmentContext)_localctx).assignRetExpr =  new BinaryExpression( ((ExpressionAssignmentContext)_localctx).lOrExpr.orExpr , ((ExpressionAssignmentContext)_localctx).rAssignExpr.assignRetExpr, BinaryOperator.assign );
						    setPosition( _localctx.assignRetExpr , ((ExpressionAssignmentContext)_localctx).assign.getLine() , ((ExpressionAssignmentContext)_localctx).assign.getCharPositionInLine() );
						
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(245);
				((ExpressionAssignmentContext)_localctx).singleOrExpr = expressionOr();

					        ((ExpressionAssignmentContext)_localctx).assignRetExpr =  ((ExpressionAssignmentContext)_localctx).singleOrExpr.orExpr;
					    
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ExpressionOrContext extends ParserRuleContext {
		public Expression orExpr;
		public ExpressionAndContext andExpr;
		public ExpressionOrTempContext finalOrExpr;
		public ExpressionAndContext expressionAnd() {
			return getRuleContext(ExpressionAndContext.class,0);
		}
		public ExpressionOrTempContext expressionOrTemp() {
			return getRuleContext(ExpressionOrTempContext.class,0);
		}
		public ExpressionOrContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_expressionOr; }
	}

	public final ExpressionOrContext expressionOr() throws RecognitionException {
		ExpressionOrContext _localctx = new ExpressionOrContext(_ctx, getState());
		enterRule(_localctx, 28, RULE_expressionOr);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(250);
			((ExpressionOrContext)_localctx).andExpr = expressionAnd();
			setState(251);
			((ExpressionOrContext)_localctx).finalOrExpr = expressionOrTemp( ((ExpressionOrContext)_localctx).andExpr.andExpr );

					    ((ExpressionOrContext)_localctx).orExpr =  ((ExpressionOrContext)_localctx).finalOrExpr.multipleOrExpr;
					
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ExpressionOrTempContext extends ParserRuleContext {
		public Expression orExpr;
		public Expression multipleOrExpr;
		public BinaryExpression realOrExpr;
		public Token orOp;
		public ExpressionAndContext andExpr;
		public ExpressionOrTempContext retMultipleOrExpr;
		public ExpressionAndContext expressionAnd() {
			return getRuleContext(ExpressionAndContext.class,0);
		}
		public ExpressionOrTempContext expressionOrTemp() {
			return getRuleContext(ExpressionOrTempContext.class,0);
		}
		public ExpressionOrTempContext(ParserRuleContext parent, int invokingState) { super(parent, invokingState); }
		public ExpressionOrTempContext(ParserRuleContext parent, int invokingState, Expression orExpr) {
			super(parent, invokingState);
			this.orExpr = orExpr;
		}
		@Override public int getRuleIndex() { return RULE_expressionOrTemp; }
	}

	public final ExpressionOrTempContext expressionOrTemp(Expression orExpr) throws RecognitionException {
		ExpressionOrTempContext _localctx = new ExpressionOrTempContext(_ctx, getState(), orExpr);
		enterRule(_localctx, 30, RULE_expressionOrTemp);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(261);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__20:
				{
				setState(254);
				((ExpressionOrTempContext)_localctx).orOp = match(T__20);
				setState(255);
				((ExpressionOrTempContext)_localctx).andExpr = expressionAnd();

						    ((ExpressionOrTempContext)_localctx).realOrExpr =  new BinaryExpression( _localctx.orExpr , ((ExpressionOrTempContext)_localctx).andExpr.andExpr , BinaryOperator.or );
						    setPosition( _localctx.realOrExpr , ((ExpressionOrTempContext)_localctx).orOp.getLine() , ((ExpressionOrTempContext)_localctx).orOp.getCharPositionInLine() );
						
				setState(257);
				((ExpressionOrTempContext)_localctx).retMultipleOrExpr = expressionOrTemp( _localctx.realOrExpr );

						    ((ExpressionOrTempContext)_localctx).multipleOrExpr =  ((ExpressionOrTempContext)_localctx).retMultipleOrExpr.multipleOrExpr;
						
				}
				break;
			case T__7:
			case T__12:
			case T__13:
			case T__19:
			case T__32:
				{

				            ((ExpressionOrTempContext)_localctx).multipleOrExpr =  _localctx.orExpr;
					    
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ExpressionAndContext extends ParserRuleContext {
		public Expression andExpr;
		public ExpressionEqContext eqExpr;
		public ExpressionAndTempContext retMultipleAndExpr;
		public ExpressionEqContext expressionEq() {
			return getRuleContext(ExpressionEqContext.class,0);
		}
		public ExpressionAndTempContext expressionAndTemp() {
			return getRuleContext(ExpressionAndTempContext.class,0);
		}
		public ExpressionAndContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_expressionAnd; }
	}

	public final ExpressionAndContext expressionAnd() throws RecognitionException {
		ExpressionAndContext _localctx = new ExpressionAndContext(_ctx, getState());
		enterRule(_localctx, 32, RULE_expressionAnd);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(263);
			((ExpressionAndContext)_localctx).eqExpr = expressionEq();
			setState(264);
			((ExpressionAndContext)_localctx).retMultipleAndExpr = expressionAndTemp( ((ExpressionAndContext)_localctx).eqExpr.eqExpr );

					    ((ExpressionAndContext)_localctx).andExpr =  ((ExpressionAndContext)_localctx).retMultipleAndExpr.multipleAndExpr;
					
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ExpressionAndTempContext extends ParserRuleContext {
		public Expression andExpr;
		public Expression multipleAndExpr;
		public BinaryExpression realAndExpr;
		public Token andOp;
		public ExpressionEqContext eqExpr;
		public ExpressionAndTempContext retMultipleAndExpr;
		public ExpressionEqContext expressionEq() {
			return getRuleContext(ExpressionEqContext.class,0);
		}
		public ExpressionAndTempContext expressionAndTemp() {
			return getRuleContext(ExpressionAndTempContext.class,0);
		}
		public ExpressionAndTempContext(ParserRuleContext parent, int invokingState) { super(parent, invokingState); }
		public ExpressionAndTempContext(ParserRuleContext parent, int invokingState, Expression andExpr) {
			super(parent, invokingState);
			this.andExpr = andExpr;
		}
		@Override public int getRuleIndex() { return RULE_expressionAndTemp; }
	}

	public final ExpressionAndTempContext expressionAndTemp(Expression andExpr) throws RecognitionException {
		ExpressionAndTempContext _localctx = new ExpressionAndTempContext(_ctx, getState(), andExpr);
		enterRule(_localctx, 34, RULE_expressionAndTemp);
		try {
			setState(274);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__21:
				enterOuterAlt(_localctx, 1);
				{
				setState(267);
				((ExpressionAndTempContext)_localctx).andOp = match(T__21);
				setState(268);
				((ExpressionAndTempContext)_localctx).eqExpr = expressionEq();

				            ((ExpressionAndTempContext)_localctx).realAndExpr =  new BinaryExpression( _localctx.andExpr , ((ExpressionAndTempContext)_localctx).eqExpr.eqExpr , BinaryOperator.and );
				            setPosition( _localctx.realAndExpr , ((ExpressionAndTempContext)_localctx).andOp.getLine() , ((ExpressionAndTempContext)_localctx).andOp.getCharPositionInLine() );

						
				setState(270);
				((ExpressionAndTempContext)_localctx).retMultipleAndExpr = expressionAndTemp( _localctx.realAndExpr );

						    ((ExpressionAndTempContext)_localctx).multipleAndExpr =  ((ExpressionAndTempContext)_localctx).retMultipleAndExpr.multipleAndExpr;
						
				}
				break;
			case T__7:
			case T__12:
			case T__13:
			case T__19:
			case T__20:
			case T__32:
				enterOuterAlt(_localctx, 2);
				{

				            ((ExpressionAndTempContext)_localctx).multipleAndExpr =  _localctx.andExpr;
					    
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ExpressionEqContext extends ParserRuleContext {
		public Expression eqExpr;
		public ExpressionCmpContext compExpr;
		public ExpressionEqTempContext multipleEqExpr;
		public ExpressionCmpContext expressionCmp() {
			return getRuleContext(ExpressionCmpContext.class,0);
		}
		public ExpressionEqTempContext expressionEqTemp() {
			return getRuleContext(ExpressionEqTempContext.class,0);
		}
		public ExpressionEqContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_expressionEq; }
	}

	public final ExpressionEqContext expressionEq() throws RecognitionException {
		ExpressionEqContext _localctx = new ExpressionEqContext(_ctx, getState());
		enterRule(_localctx, 36, RULE_expressionEq);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(276);
			((ExpressionEqContext)_localctx).compExpr = expressionCmp();
			setState(277);
			((ExpressionEqContext)_localctx).multipleEqExpr = expressionEqTemp( ((ExpressionEqContext)_localctx).compExpr.compExpr );

					    ((ExpressionEqContext)_localctx).eqExpr =  ((ExpressionEqContext)_localctx).multipleEqExpr.retMultipleEqExpr;
					
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ExpressionEqTempContext extends ParserRuleContext {
		public Expression eqExpr;
		public Expression retMultipleEqExpr;
		public BinaryExpression realEqExpr;
		public BinaryOperator eqBinOp;
		public Token eqOp;
		public ExpressionCmpContext compExpr;
		public ExpressionEqTempContext multipleEqExpr;
		public ExpressionCmpContext expressionCmp() {
			return getRuleContext(ExpressionCmpContext.class,0);
		}
		public ExpressionEqTempContext expressionEqTemp() {
			return getRuleContext(ExpressionEqTempContext.class,0);
		}
		public ExpressionEqTempContext(ParserRuleContext parent, int invokingState) { super(parent, invokingState); }
		public ExpressionEqTempContext(ParserRuleContext parent, int invokingState, Expression eqExpr) {
			super(parent, invokingState);
			this.eqExpr = eqExpr;
		}
		@Override public int getRuleIndex() { return RULE_expressionEqTemp; }
	}

	public final ExpressionEqTempContext expressionEqTemp(Expression eqExpr) throws RecognitionException {
		ExpressionEqTempContext _localctx = new ExpressionEqTempContext(_ctx, getState(), eqExpr);
		enterRule(_localctx, 38, RULE_expressionEqTemp);
		int _la;
		try {
			setState(288);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__22:
			case T__23:
				enterOuterAlt(_localctx, 1);
				{
				setState(280);
				((ExpressionEqTempContext)_localctx).eqOp = _input.LT(1);
				_la = _input.LA(1);
				if ( !(_la==T__22 || _la==T__23) ) {
					((ExpressionEqTempContext)_localctx).eqOp = (Token)_errHandler.recoverInline(this);
				}
				else {
					if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
					_errHandler.reportMatch(this);
					consume();
				}

						    if( (((ExpressionEqTempContext)_localctx).eqOp!=null?((ExpressionEqTempContext)_localctx).eqOp.getText():null).equals( "==" ) )
						        ((ExpressionEqTempContext)_localctx).eqBinOp =  BinaryOperator.eq;
						    else if( (((ExpressionEqTempContext)_localctx).eqOp!=null?((ExpressionEqTempContext)_localctx).eqOp.getText():null).equals( "<>" ) )
						        ((ExpressionEqTempContext)_localctx).eqBinOp =  BinaryOperator.neq;
						
				setState(282);
				((ExpressionEqTempContext)_localctx).compExpr = expressionCmp();

						    ((ExpressionEqTempContext)_localctx).realEqExpr =  new BinaryExpression( _localctx.eqExpr , ((ExpressionEqTempContext)_localctx).compExpr.compExpr , _localctx.eqBinOp );
				            setPosition( _localctx.realEqExpr , ((ExpressionEqTempContext)_localctx).eqOp.getLine() , ((ExpressionEqTempContext)_localctx).eqOp.getCharPositionInLine() );

						 
				setState(284);
				((ExpressionEqTempContext)_localctx).multipleEqExpr = expressionEqTemp( _localctx.realEqExpr );

						    ((ExpressionEqTempContext)_localctx).retMultipleEqExpr =  ((ExpressionEqTempContext)_localctx).multipleEqExpr.retMultipleEqExpr;
						 
				}
				break;
			case T__7:
			case T__12:
			case T__13:
			case T__19:
			case T__20:
			case T__21:
			case T__32:
				enterOuterAlt(_localctx, 2);
				{

					        ((ExpressionEqTempContext)_localctx).retMultipleEqExpr =  _localctx.eqExpr;
					    
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ExpressionCmpContext extends ParserRuleContext {
		public Expression compExpr;
		public ExpressionAddContext addExpr;
		public ExpressionCmpTempContext retMultipleCompExpr;
		public ExpressionAddContext expressionAdd() {
			return getRuleContext(ExpressionAddContext.class,0);
		}
		public ExpressionCmpTempContext expressionCmpTemp() {
			return getRuleContext(ExpressionCmpTempContext.class,0);
		}
		public ExpressionCmpContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_expressionCmp; }
	}

	public final ExpressionCmpContext expressionCmp() throws RecognitionException {
		ExpressionCmpContext _localctx = new ExpressionCmpContext(_ctx, getState());
		enterRule(_localctx, 40, RULE_expressionCmp);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(290);
			((ExpressionCmpContext)_localctx).addExpr = expressionAdd();
			setState(291);
			((ExpressionCmpContext)_localctx).retMultipleCompExpr = expressionCmpTemp( ((ExpressionCmpContext)_localctx).addExpr.addExpr );

					    ((ExpressionCmpContext)_localctx).compExpr =  ((ExpressionCmpContext)_localctx).retMultipleCompExpr.retMultipleCompExpr;
					
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ExpressionCmpTempContext extends ParserRuleContext {
		public Expression compExpr;
		public Expression retMultipleCompExpr;
		public BinaryExpression realCompExpr;
		public BinaryOperator compBinOp;
		public Token relatOp;
		public ExpressionAddContext addExpr;
		public ExpressionCmpTempContext multipleCompExpr;
		public ExpressionAddContext expressionAdd() {
			return getRuleContext(ExpressionAddContext.class,0);
		}
		public ExpressionCmpTempContext expressionCmpTemp() {
			return getRuleContext(ExpressionCmpTempContext.class,0);
		}
		public ExpressionCmpTempContext(ParserRuleContext parent, int invokingState) { super(parent, invokingState); }
		public ExpressionCmpTempContext(ParserRuleContext parent, int invokingState, Expression compExpr) {
			super(parent, invokingState);
			this.compExpr = compExpr;
		}
		@Override public int getRuleIndex() { return RULE_expressionCmpTemp; }
	}

	public final ExpressionCmpTempContext expressionCmpTemp(Expression compExpr) throws RecognitionException {
		ExpressionCmpTempContext _localctx = new ExpressionCmpTempContext(_ctx, getState(), compExpr);
		enterRule(_localctx, 42, RULE_expressionCmpTemp);
		int _la;
		try {
			setState(302);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__24:
			case T__25:
				enterOuterAlt(_localctx, 1);
				{
				setState(294);
				((ExpressionCmpTempContext)_localctx).relatOp = _input.LT(1);
				_la = _input.LA(1);
				if ( !(_la==T__24 || _la==T__25) ) {
					((ExpressionCmpTempContext)_localctx).relatOp = (Token)_errHandler.recoverInline(this);
				}
				else {
					if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
					_errHandler.reportMatch(this);
					consume();
				}

						        if( (((ExpressionCmpTempContext)_localctx).relatOp!=null?((ExpressionCmpTempContext)_localctx).relatOp.getText():null).equals( ">" ) )
						        {
						            ((ExpressionCmpTempContext)_localctx).compBinOp =  BinaryOperator.gt;
						        }
						        else if( (((ExpressionCmpTempContext)_localctx).relatOp!=null?((ExpressionCmpTempContext)_localctx).relatOp.getText():null).equals( "<" ) )
						        {
						            ((ExpressionCmpTempContext)_localctx).compBinOp =  BinaryOperator.lt;
						        }
						     
				setState(296);
				((ExpressionCmpTempContext)_localctx).addExpr = expressionAdd();

						        ((ExpressionCmpTempContext)_localctx).realCompExpr =  new BinaryExpression( _localctx.compExpr , ((ExpressionCmpTempContext)_localctx).addExpr.addExpr , _localctx.compBinOp );
				                setPosition( _localctx.realCompExpr , ((ExpressionCmpTempContext)_localctx).relatOp.getLine() , ((ExpressionCmpTempContext)_localctx).relatOp.getCharPositionInLine() );

						    
				setState(298);
				((ExpressionCmpTempContext)_localctx).multipleCompExpr = expressionCmpTemp( _localctx.realCompExpr );

						        ((ExpressionCmpTempContext)_localctx).retMultipleCompExpr =  ((ExpressionCmpTempContext)_localctx).multipleCompExpr.retMultipleCompExpr;
						    
				}
				break;
			case T__7:
			case T__12:
			case T__13:
			case T__19:
			case T__20:
			case T__21:
			case T__22:
			case T__23:
			case T__32:
				enterOuterAlt(_localctx, 2);
				{

				                ((ExpressionCmpTempContext)_localctx).retMultipleCompExpr =  _localctx.compExpr;
				            
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ExpressionAddContext extends ParserRuleContext {
		public Expression addExpr;
		public ExpressionMultContext multExpr;
		public ExpressionAddTempContext multipleAddExpr;
		public ExpressionMultContext expressionMult() {
			return getRuleContext(ExpressionMultContext.class,0);
		}
		public ExpressionAddTempContext expressionAddTemp() {
			return getRuleContext(ExpressionAddTempContext.class,0);
		}
		public ExpressionAddContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_expressionAdd; }
	}

	public final ExpressionAddContext expressionAdd() throws RecognitionException {
		ExpressionAddContext _localctx = new ExpressionAddContext(_ctx, getState());
		enterRule(_localctx, 44, RULE_expressionAdd);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(304);
			((ExpressionAddContext)_localctx).multExpr = expressionMult();
			setState(305);
			((ExpressionAddContext)_localctx).multipleAddExpr = expressionAddTemp( ((ExpressionAddContext)_localctx).multExpr.multExpr );

					    ((ExpressionAddContext)_localctx).addExpr =  ((ExpressionAddContext)_localctx).multipleAddExpr.retMultipleAddExpr;
					
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ExpressionAddTempContext extends ParserRuleContext {
		public Expression addExpr;
		public Expression retMultipleAddExpr;
		public BinaryExpression realAddExpr;
		public BinaryOperator addBinOp;
		public Token addOp;
		public ExpressionMultContext multExpr;
		public ExpressionAddTempContext multipleAddExpr;
		public ExpressionMultContext expressionMult() {
			return getRuleContext(ExpressionMultContext.class,0);
		}
		public ExpressionAddTempContext expressionAddTemp() {
			return getRuleContext(ExpressionAddTempContext.class,0);
		}
		public ExpressionAddTempContext(ParserRuleContext parent, int invokingState) { super(parent, invokingState); }
		public ExpressionAddTempContext(ParserRuleContext parent, int invokingState, Expression addExpr) {
			super(parent, invokingState);
			this.addExpr = addExpr;
		}
		@Override public int getRuleIndex() { return RULE_expressionAddTemp; }
	}

	public final ExpressionAddTempContext expressionAddTemp(Expression addExpr) throws RecognitionException {
		ExpressionAddTempContext _localctx = new ExpressionAddTempContext(_ctx, getState(), addExpr);
		enterRule(_localctx, 46, RULE_expressionAddTemp);
		int _la;
		try {
			setState(316);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__26:
			case T__27:
				enterOuterAlt(_localctx, 1);
				{
				setState(308);
				((ExpressionAddTempContext)_localctx).addOp = _input.LT(1);
				_la = _input.LA(1);
				if ( !(_la==T__26 || _la==T__27) ) {
					((ExpressionAddTempContext)_localctx).addOp = (Token)_errHandler.recoverInline(this);
				}
				else {
					if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
					_errHandler.reportMatch(this);
					consume();
				}

						        if( (((ExpressionAddTempContext)_localctx).addOp!=null?((ExpressionAddTempContext)_localctx).addOp.getText():null).equals( "+" ) )
						            ((ExpressionAddTempContext)_localctx).addBinOp =  BinaryOperator.add;
						        else if( (((ExpressionAddTempContext)_localctx).addOp!=null?((ExpressionAddTempContext)_localctx).addOp.getText():null).equals( "-" ) )
						            ((ExpressionAddTempContext)_localctx).addBinOp =  BinaryOperator.sub;
						    
				setState(310);
				((ExpressionAddTempContext)_localctx).multExpr = expressionMult();

						    ((ExpressionAddTempContext)_localctx).realAddExpr =  new BinaryExpression( _localctx.addExpr , ((ExpressionAddTempContext)_localctx).multExpr.multExpr , _localctx.addBinOp );
				            setPosition( _localctx.realAddExpr , ((ExpressionAddTempContext)_localctx).addOp.getLine() , ((ExpressionAddTempContext)_localctx).addOp.getCharPositionInLine() );
						
				setState(312);
				((ExpressionAddTempContext)_localctx).multipleAddExpr = expressionAddTemp( _localctx.realAddExpr );

						    ((ExpressionAddTempContext)_localctx).retMultipleAddExpr =  ((ExpressionAddTempContext)_localctx).multipleAddExpr.retMultipleAddExpr;
						
				}
				break;
			case T__7:
			case T__12:
			case T__13:
			case T__19:
			case T__20:
			case T__21:
			case T__22:
			case T__23:
			case T__24:
			case T__25:
			case T__32:
				enterOuterAlt(_localctx, 2);
				{

					        ((ExpressionAddTempContext)_localctx).retMultipleAddExpr =  _localctx.addExpr;
					    
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ExpressionMultContext extends ParserRuleContext {
		public Expression multExpr;
		public ExpressionUnaryContext unaryExpr;
		public ExpressionMultTempContext retMultipleMultExpr;
		public ExpressionUnaryContext expressionUnary() {
			return getRuleContext(ExpressionUnaryContext.class,0);
		}
		public ExpressionMultTempContext expressionMultTemp() {
			return getRuleContext(ExpressionMultTempContext.class,0);
		}
		public ExpressionMultContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_expressionMult; }
	}

	public final ExpressionMultContext expressionMult() throws RecognitionException {
		ExpressionMultContext _localctx = new ExpressionMultContext(_ctx, getState());
		enterRule(_localctx, 48, RULE_expressionMult);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(318);
			((ExpressionMultContext)_localctx).unaryExpr = expressionUnary();
			setState(319);
			((ExpressionMultContext)_localctx).retMultipleMultExpr = expressionMultTemp( ((ExpressionMultContext)_localctx).unaryExpr.unaryExpr );

					    ((ExpressionMultContext)_localctx).multExpr =  ((ExpressionMultContext)_localctx).retMultipleMultExpr.retMultipleMultExpr;
					
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ExpressionMultTempContext extends ParserRuleContext {
		public Expression multExpr;
		public Expression retMultipleMultExpr;
		public BinaryOperator multBinOp;
		public BinaryExpression realMultExpr;
		public Token multOp;
		public ExpressionUnaryContext unaryExpr;
		public ExpressionMultTempContext multipleMultExpr;
		public ExpressionUnaryContext expressionUnary() {
			return getRuleContext(ExpressionUnaryContext.class,0);
		}
		public ExpressionMultTempContext expressionMultTemp() {
			return getRuleContext(ExpressionMultTempContext.class,0);
		}
		public ExpressionMultTempContext(ParserRuleContext parent, int invokingState) { super(parent, invokingState); }
		public ExpressionMultTempContext(ParserRuleContext parent, int invokingState, Expression multExpr) {
			super(parent, invokingState);
			this.multExpr = multExpr;
		}
		@Override public int getRuleIndex() { return RULE_expressionMultTemp; }
	}

	public final ExpressionMultTempContext expressionMultTemp(Expression multExpr) throws RecognitionException {
		ExpressionMultTempContext _localctx = new ExpressionMultTempContext(_ctx, getState(), multExpr);
		enterRule(_localctx, 50, RULE_expressionMultTemp);
		int _la;
		try {
			setState(330);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__28:
			case T__29:
				enterOuterAlt(_localctx, 1);
				{
				setState(322);
				((ExpressionMultTempContext)_localctx).multOp = _input.LT(1);
				_la = _input.LA(1);
				if ( !(_la==T__28 || _la==T__29) ) {
					((ExpressionMultTempContext)_localctx).multOp = (Token)_errHandler.recoverInline(this);
				}
				else {
					if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
					_errHandler.reportMatch(this);
					consume();
				}

				        		        if( (((ExpressionMultTempContext)_localctx).multOp!=null?((ExpressionMultTempContext)_localctx).multOp.getText():null).equals( "*" ) )
				        		            ((ExpressionMultTempContext)_localctx).multBinOp =  BinaryOperator.mult;
				        		        else if( (((ExpressionMultTempContext)_localctx).multOp!=null?((ExpressionMultTempContext)_localctx).multOp.getText():null).equals( "/" ) )
				        		            ((ExpressionMultTempContext)_localctx).multBinOp =  BinaryOperator.div;
				        		    
				setState(324);
				((ExpressionMultTempContext)_localctx).unaryExpr = expressionUnary();

						    ((ExpressionMultTempContext)_localctx).realMultExpr =  new BinaryExpression( _localctx.multExpr , ((ExpressionMultTempContext)_localctx).unaryExpr.unaryExpr , _localctx.multBinOp );
				            setPosition( _localctx.realMultExpr , ((ExpressionMultTempContext)_localctx).multOp.getLine() , ((ExpressionMultTempContext)_localctx).multOp.getCharPositionInLine() );
						
				setState(326);
				((ExpressionMultTempContext)_localctx).multipleMultExpr = expressionMultTemp( _localctx.realMultExpr );

						    ((ExpressionMultTempContext)_localctx).retMultipleMultExpr =  ((ExpressionMultTempContext)_localctx).multipleMultExpr.retMultipleMultExpr;
						
				}
				break;
			case T__7:
			case T__12:
			case T__13:
			case T__19:
			case T__20:
			case T__21:
			case T__22:
			case T__23:
			case T__24:
			case T__25:
			case T__26:
			case T__27:
			case T__32:
				enterOuterAlt(_localctx, 2);
				{

					        ((ExpressionMultTempContext)_localctx).retMultipleMultExpr =  _localctx.multExpr;
					    
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ExpressionUnaryContext extends ParserRuleContext {
		public Expression unaryExpr;
		public UnaryOperator uOp;
		public Token notOp;
		public ExpressionUnaryContext unaryOperand;
		public ExpressionMemContext memExpr;
		public ExpressionUnaryContext expressionUnary() {
			return getRuleContext(ExpressionUnaryContext.class,0);
		}
		public ExpressionMemContext expressionMem() {
			return getRuleContext(ExpressionMemContext.class,0);
		}
		public ExpressionUnaryContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_expressionUnary; }
	}

	public final ExpressionUnaryContext expressionUnary() throws RecognitionException {
		ExpressionUnaryContext _localctx = new ExpressionUnaryContext(_ctx, getState());
		enterRule(_localctx, 52, RULE_expressionUnary);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(340);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__27:
			case T__30:
				{
				setState(332);
				((ExpressionUnaryContext)_localctx).notOp = _input.LT(1);
				_la = _input.LA(1);
				if ( !(_la==T__27 || _la==T__30) ) {
					((ExpressionUnaryContext)_localctx).notOp = (Token)_errHandler.recoverInline(this);
				}
				else {
					if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
					_errHandler.reportMatch(this);
					consume();
				}

				                if( (((ExpressionUnaryContext)_localctx).notOp!=null?((ExpressionUnaryContext)_localctx).notOp.getText():null).equals( "!" ) )
				                    ((ExpressionUnaryContext)_localctx).uOp =  UnaryOperator.not;
				                else if( (((ExpressionUnaryContext)_localctx).notOp!=null?((ExpressionUnaryContext)_localctx).notOp.getText():null).equals( "-" ) )
				                    ((ExpressionUnaryContext)_localctx).uOp =  UnaryOperator.minus;
				            
				setState(334);
				((ExpressionUnaryContext)_localctx).unaryOperand = expressionUnary();

				                ((ExpressionUnaryContext)_localctx).unaryExpr =  new UnaryExpression( _localctx.uOp , ((ExpressionUnaryContext)_localctx).unaryOperand.unaryExpr );
				                setPosition( _localctx.unaryExpr , ((ExpressionUnaryContext)_localctx).notOp.getLine() , ((ExpressionUnaryContext)_localctx).notOp.getCharPositionInLine() );
				            
				}
				break;
			case T__11:
			case T__35:
			case T__36:
			case T__37:
			case T__38:
			case CONST_NUM:
			case CONST_STR:
			case ID:
				{
				setState(337);
				((ExpressionUnaryContext)_localctx).memExpr = expressionMem();

				                ((ExpressionUnaryContext)_localctx).unaryExpr =  ((ExpressionUnaryContext)_localctx).memExpr.memExpr;
				            
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ExpressionMemContext extends ParserRuleContext {
		public Expression memExpr;
		public ExpressionMethodsContext methodExpr;
		public ExpressionMemTempContext arrExpr;
		public ExpressionMethodsContext expressionMethods() {
			return getRuleContext(ExpressionMethodsContext.class,0);
		}
		public ExpressionMemTempContext expressionMemTemp() {
			return getRuleContext(ExpressionMemTempContext.class,0);
		}
		public ExpressionMemContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_expressionMem; }
	}

	public final ExpressionMemContext expressionMem() throws RecognitionException {
		ExpressionMemContext _localctx = new ExpressionMemContext(_ctx, getState());
		enterRule(_localctx, 54, RULE_expressionMem);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(342);
			((ExpressionMemContext)_localctx).methodExpr = expressionMethods();
			setState(343);
			((ExpressionMemContext)_localctx).arrExpr = expressionMemTemp( ((ExpressionMemContext)_localctx).methodExpr.methodExpr );

					    ((ExpressionMemContext)_localctx).memExpr =  ((ExpressionMemContext)_localctx).arrExpr.realArrExpr;
					
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ExpressionMemTempContext extends ParserRuleContext {
		public Expression arrExpr;
		public Expression realArrExpr;
		public ExpressionContext subscript;
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public ExpressionMemTempContext(ParserRuleContext parent, int invokingState) { super(parent, invokingState); }
		public ExpressionMemTempContext(ParserRuleContext parent, int invokingState, Expression arrExpr) {
			super(parent, invokingState);
			this.arrExpr = arrExpr;
		}
		@Override public int getRuleIndex() { return RULE_expressionMemTemp; }
	}

	public final ExpressionMemTempContext expressionMemTemp(Expression arrExpr) throws RecognitionException {
		ExpressionMemTempContext _localctx = new ExpressionMemTempContext(_ctx, getState(), arrExpr);
		enterRule(_localctx, 56, RULE_expressionMemTemp);
		try {
			setState(352);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__31:
				enterOuterAlt(_localctx, 1);
				{
				setState(346);
				match(T__31);
				setState(347);
				((ExpressionMemTempContext)_localctx).subscript = expression();
				setState(348);
				match(T__32);

				            ((ExpressionMemTempContext)_localctx).realArrExpr =  new ArrayCall( _localctx.arrExpr , ((ExpressionMemTempContext)_localctx).subscript.finalExpr );
				            setPosition( _localctx.realArrExpr , _localctx.arrExpr.getLineNum() , _localctx.arrExpr.getColNum() );
						
				}
				break;
			case T__7:
			case T__12:
			case T__13:
			case T__19:
			case T__20:
			case T__21:
			case T__22:
			case T__23:
			case T__24:
			case T__25:
			case T__26:
			case T__27:
			case T__28:
			case T__29:
			case T__32:
				enterOuterAlt(_localctx, 2);
				{

				            ((ExpressionMemTempContext)_localctx).realArrExpr =  _localctx.arrExpr;
					    
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ExpressionMethodsContext extends ParserRuleContext {
		public Expression methodExpr;
		public ExpressionOtherContext otherExpr;
		public ExpressionMethodsTempContext retMethodExpr;
		public ExpressionOtherContext expressionOther() {
			return getRuleContext(ExpressionOtherContext.class,0);
		}
		public ExpressionMethodsTempContext expressionMethodsTemp() {
			return getRuleContext(ExpressionMethodsTempContext.class,0);
		}
		public ExpressionMethodsContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_expressionMethods; }
	}

	public final ExpressionMethodsContext expressionMethods() throws RecognitionException {
		ExpressionMethodsContext _localctx = new ExpressionMethodsContext(_ctx, getState());
		enterRule(_localctx, 58, RULE_expressionMethods);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(354);
			((ExpressionMethodsContext)_localctx).otherExpr = expressionOther();
			setState(355);
			((ExpressionMethodsContext)_localctx).retMethodExpr = expressionMethodsTemp( ((ExpressionMethodsContext)_localctx).otherExpr.otherExpr );

				        ((ExpressionMethodsContext)_localctx).methodExpr =  ((ExpressionMethodsContext)_localctx).retMethodExpr.realMethodCallExpr;
				    
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ExpressionMethodsTempContext extends ParserRuleContext {
		public Expression instance;
		public Expression realMethodCallExpr;
		public Expression methodCallExpr;
		public Token methodName;
		public ExpressionContext argExpr;
		public ExpressionMethodsTempContext retMethodCallExpr;
		public ExpressionMethodsTempContext expressionMethodsTemp() {
			return getRuleContext(ExpressionMethodsTempContext.class,0);
		}
		public TerminalNode ID() { return getToken(SmoolaParser.ID, 0); }
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public ExpressionMethodsTempContext(ParserRuleContext parent, int invokingState) { super(parent, invokingState); }
		public ExpressionMethodsTempContext(ParserRuleContext parent, int invokingState, Expression instance) {
			super(parent, invokingState);
			this.instance = instance;
		}
		@Override public int getRuleIndex() { return RULE_expressionMethodsTemp; }
	}

	public final ExpressionMethodsTempContext expressionMethodsTemp(Expression instance) throws RecognitionException {
		ExpressionMethodsTempContext _localctx = new ExpressionMethodsTempContext(_ctx, getState(), instance);
		enterRule(_localctx, 60, RULE_expressionMethodsTemp);
		int _la;
		try {
			setState(386);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__33:
				enterOuterAlt(_localctx, 1);
				{
				setState(358);
				match(T__33);
				setState(380);
				_errHandler.sync(this);
				switch ( getInterpreter().adaptivePredict(_input,20,_ctx) ) {
				case 1:
					{
					setState(359);
					((ExpressionMethodsTempContext)_localctx).methodName = match(ID);
					setState(360);
					match(T__3);

						        ((ExpressionMethodsTempContext)_localctx).methodCallExpr =  new MethodCall( _localctx.instance , new Identifier( (((ExpressionMethodsTempContext)_localctx).methodName!=null?((ExpressionMethodsTempContext)_localctx).methodName.getText():null) ) );
					            setPosition( ( ( MethodCall ) _localctx.methodCallExpr ).getMethodName() , ((ExpressionMethodsTempContext)_localctx).methodName.getLine() , ((ExpressionMethodsTempContext)_localctx).methodName.getCharPositionInLine() );

						    
					}
					break;
				case 2:
					{
					setState(362);
					((ExpressionMethodsTempContext)_localctx).methodName = match(ID);

						        ((ExpressionMethodsTempContext)_localctx).methodCallExpr =  new MethodCall( _localctx.instance , new Identifier( (((ExpressionMethodsTempContext)_localctx).methodName!=null?((ExpressionMethodsTempContext)_localctx).methodName.getText():null) ) );
						        setPosition( ( ( MethodCall ) _localctx.methodCallExpr ).getMethodName() , ((ExpressionMethodsTempContext)_localctx).methodName.getLine() , ((ExpressionMethodsTempContext)_localctx).methodName.getCharPositionInLine() );
						    
					setState(364);
					match(T__11);
					{
					setState(365);
					((ExpressionMethodsTempContext)_localctx).argExpr = expression();

						        ( ( MethodCall ) _localctx.methodCallExpr ).addArg( ((ExpressionMethodsTempContext)_localctx).argExpr.finalExpr );
						    
					setState(373);
					_errHandler.sync(this);
					_la = _input.LA(1);
					while (_la==T__12) {
						{
						{
						setState(367);
						match(T__12);
						setState(368);
						((ExpressionMethodsTempContext)_localctx).argExpr = expression();

							        ( ( MethodCall ) _localctx.methodCallExpr ).addArg( ((ExpressionMethodsTempContext)_localctx).argExpr.finalExpr );
							    
						}
						}
						setState(375);
						_errHandler.sync(this);
						_la = _input.LA(1);
					}
					}
					setState(376);
					match(T__13);
					}
					break;
				case 3:
					{
					setState(378);
					match(T__34);

						        ((ExpressionMethodsTempContext)_localctx).methodCallExpr =  new Length( _localctx.instance );
						    
					}
					break;
				}
				setState(382);
				((ExpressionMethodsTempContext)_localctx).retMethodCallExpr = expressionMethodsTemp( _localctx.methodCallExpr );

					        ((ExpressionMethodsTempContext)_localctx).realMethodCallExpr =  ((ExpressionMethodsTempContext)_localctx).retMethodCallExpr.realMethodCallExpr;
					    
				}
				break;
			case T__7:
			case T__12:
			case T__13:
			case T__19:
			case T__20:
			case T__21:
			case T__22:
			case T__23:
			case T__24:
			case T__25:
			case T__26:
			case T__27:
			case T__28:
			case T__29:
			case T__31:
			case T__32:
				enterOuterAlt(_localctx, 2);
				{

					        ((ExpressionMethodsTempContext)_localctx).realMethodCallExpr =  _localctx.instance;
					    
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ExpressionOtherContext extends ParserRuleContext {
		public Expression otherExpr;
		public Token number;
		public Token string;
		public Token newExpr;
		public Token arraySize;
		public Token className;
		public Token thisExpr;
		public Token trueExpr;
		public Token falseExpr;
		public Token id;
		public Token leftPara;
		public ExpressionContext paraExpr;
		public TerminalNode CONST_NUM() { return getToken(SmoolaParser.CONST_NUM, 0); }
		public TerminalNode CONST_STR() { return getToken(SmoolaParser.CONST_STR, 0); }
		public TerminalNode ID() { return getToken(SmoolaParser.ID, 0); }
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public ExpressionOtherContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_expressionOther; }
	}

	public final ExpressionOtherContext expressionOther() throws RecognitionException {
		ExpressionOtherContext _localctx = new ExpressionOtherContext(_ctx, getState());
		enterRule(_localctx, 62, RULE_expressionOther);
		try {
			setState(415);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,22,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				{
				setState(388);
				((ExpressionOtherContext)_localctx).number = match(CONST_NUM);

				            ((ExpressionOtherContext)_localctx).otherExpr =  new IntValue( (((ExpressionOtherContext)_localctx).number!=null?Integer.valueOf(((ExpressionOtherContext)_localctx).number.getText()):0) , new IntType() );
				           setPosition( _localctx.otherExpr , ((ExpressionOtherContext)_localctx).number.getLine() , ((ExpressionOtherContext)_localctx).number.getCharPositionInLine() );

				        
				}
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				{
				setState(390);
				((ExpressionOtherContext)_localctx).string = match(CONST_STR);

				            ((ExpressionOtherContext)_localctx).otherExpr =  new StringValue( (((ExpressionOtherContext)_localctx).string!=null?((ExpressionOtherContext)_localctx).string.getText():null) , new StringType() );
				            setPosition( _localctx.otherExpr , ((ExpressionOtherContext)_localctx).string.getLine() , ((ExpressionOtherContext)_localctx).string.getCharPositionInLine() );

				        
				}
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				{
				setState(392);
				((ExpressionOtherContext)_localctx).newExpr = match(T__35);
				setState(393);
				match(T__5);
				setState(394);
				match(T__31);
				setState(395);
				((ExpressionOtherContext)_localctx).arraySize = match(CONST_NUM);
				setState(396);
				match(T__32);

				            ((ExpressionOtherContext)_localctx).otherExpr =  new NewArray();
				            ( ( NewArray ) _localctx.otherExpr ).setExpression( new IntValue( (((ExpressionOtherContext)_localctx).arraySize!=null?Integer.valueOf(((ExpressionOtherContext)_localctx).arraySize.getText()):0) , new IntType() ) );
				            setPosition( _localctx.otherExpr , ((ExpressionOtherContext)_localctx).newExpr.getLine() , ((ExpressionOtherContext)_localctx).newExpr.getCharPositionInLine() );
				            setPosition( ( ( NewArray ) _localctx.otherExpr ).getExpression() , ((ExpressionOtherContext)_localctx).arraySize.getLine() , ((ExpressionOtherContext)_localctx).arraySize.getCharPositionInLine() );

				        
				}
				}
				break;
			case 4:
				enterOuterAlt(_localctx, 4);
				{
				{
				setState(398);
				((ExpressionOtherContext)_localctx).newExpr = match(T__35);
				setState(399);
				((ExpressionOtherContext)_localctx).className = match(ID);
				setState(400);
				match(T__3);

				            ((ExpressionOtherContext)_localctx).otherExpr =  new NewClass( new Identifier( (((ExpressionOtherContext)_localctx).className!=null?((ExpressionOtherContext)_localctx).className.getText():null) ) );
				            Identifier newClassName = ( ( NewClass ) _localctx.otherExpr ).getClassName();
				            setPosition( newClassName , ((ExpressionOtherContext)_localctx).className.getLine()  , ((ExpressionOtherContext)_localctx).className.getCharPositionInLine() );
				            setPosition( _localctx.otherExpr , ((ExpressionOtherContext)_localctx).newExpr.getLine()  , ((ExpressionOtherContext)_localctx).newExpr.getCharPositionInLine() );

				        
				}
				}
				break;
			case 5:
				enterOuterAlt(_localctx, 5);
				{
				{
				setState(402);
				((ExpressionOtherContext)_localctx).thisExpr = match(T__36);

				            ((ExpressionOtherContext)_localctx).otherExpr =  new This();
				            setPosition( _localctx.otherExpr , ((ExpressionOtherContext)_localctx).thisExpr.getLine()  , ((ExpressionOtherContext)_localctx).thisExpr.getCharPositionInLine() );

				        
				}
				}
				break;
			case 6:
				enterOuterAlt(_localctx, 6);
				{
				{
				setState(404);
				((ExpressionOtherContext)_localctx).trueExpr = match(T__37);

				            ((ExpressionOtherContext)_localctx).otherExpr =  new BooleanValue( true , new BooleanType() );
				            setPosition( _localctx.otherExpr , ((ExpressionOtherContext)_localctx).trueExpr.getLine()  , ((ExpressionOtherContext)_localctx).trueExpr.getCharPositionInLine() );
				        
				}
				}
				break;
			case 7:
				enterOuterAlt(_localctx, 7);
				{
				{
				setState(406);
				((ExpressionOtherContext)_localctx).falseExpr = match(T__38);

				            ((ExpressionOtherContext)_localctx).otherExpr =  new BooleanValue( false , new BooleanType() );
				            setPosition( _localctx.otherExpr , ((ExpressionOtherContext)_localctx).falseExpr.getLine()  , ((ExpressionOtherContext)_localctx).falseExpr.getCharPositionInLine() );

				        
				}
				}
				break;
			case 8:
				enterOuterAlt(_localctx, 8);
				{
				{
				setState(408);
				((ExpressionOtherContext)_localctx).id = match(ID);

				            ((ExpressionOtherContext)_localctx).otherExpr =  new Identifier( (((ExpressionOtherContext)_localctx).id!=null?((ExpressionOtherContext)_localctx).id.getText():null) );
				            setPosition( _localctx.otherExpr , ((ExpressionOtherContext)_localctx).id.getLine() , ((ExpressionOtherContext)_localctx).id.getCharPositionInLine() );
				        
				}
				}
				break;
			case 9:
				enterOuterAlt(_localctx, 9);
				{
				{
				setState(410);
				((ExpressionOtherContext)_localctx).leftPara = match(T__11);
				setState(411);
				((ExpressionOtherContext)_localctx).paraExpr = expression();
				setState(412);
				match(T__13);

				            ((ExpressionOtherContext)_localctx).otherExpr =  ((ExpressionOtherContext)_localctx).paraExpr.finalExpr;
				            setPosition( _localctx.otherExpr , ((ExpressionOtherContext)_localctx).leftPara.getLine() , ((ExpressionOtherContext)_localctx).leftPara.getCharPositionInLine() );
				        
				}
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class TypeContext extends ParserRuleContext {
		public Type returnedType;
		public Token classType;
		public TerminalNode ID() { return getToken(SmoolaParser.ID, 0); }
		public TypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_type; }
	}

	public final TypeContext type() throws RecognitionException {
		TypeContext _localctx = new TypeContext(_ctx, getState());
		enterRule(_localctx, 64, RULE_type);
		try {
			setState(427);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__5:
				enterOuterAlt(_localctx, 1);
				{
				setState(417);
				match(T__5);
				 ((TypeContext)_localctx).returnedType =  new IntType(); 
				}
				break;
			case T__39:
				enterOuterAlt(_localctx, 2);
				{
				setState(419);
				match(T__39);
				 ((TypeContext)_localctx).returnedType =  new BooleanType(); 
				}
				break;
			case T__40:
				enterOuterAlt(_localctx, 3);
				{
				setState(421);
				match(T__40);
				 ((TypeContext)_localctx).returnedType =  new StringType(); 
				}
				break;
			case T__41:
				enterOuterAlt(_localctx, 4);
				{
				setState(423);
				match(T__41);
				 ((TypeContext)_localctx).returnedType =  new ArrayType(); 
				}
				break;
			case ID:
				enterOuterAlt(_localctx, 5);
				{
				setState(425);
				((TypeContext)_localctx).classType = match(ID);

					        ((TypeContext)_localctx).returnedType =  new UserDefinedType();
					        ( ( UserDefinedType ) _localctx.returnedType).setName( new Identifier( (((TypeContext)_localctx).classType!=null?((TypeContext)_localctx).classType.getText():null) ) );
					        setPosition( _localctx.returnedType , ((TypeContext)_localctx).classType.getLine() , ((TypeContext)_localctx).classType.getCharPositionInLine() );
					    
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\3\62\u01b0\4\2\t\2"+
		"\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13"+
		"\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22\t\22"+
		"\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30\4\31\t\31"+
		"\4\32\t\32\4\33\t\33\4\34\t\34\4\35\t\35\4\36\t\36\4\37\t\37\4 \t \4!"+
		"\t!\4\"\t\"\3\2\3\2\3\2\3\2\3\2\3\2\7\2K\n\2\f\2\16\2N\13\2\3\2\3\2\3"+
		"\2\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3"+
		"\3\3\3\3\3\4\3\4\3\4\3\4\3\4\3\4\5\4l\n\4\3\4\3\4\3\4\3\4\7\4r\n\4\f\4"+
		"\16\4u\13\4\3\4\3\4\3\4\7\4z\n\4\f\4\16\4}\13\4\3\4\3\4\3\5\3\5\3\5\3"+
		"\5\3\5\3\5\3\5\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6"+
		"\3\6\7\6\u0097\n\6\f\6\16\6\u009a\13\6\3\6\3\6\5\6\u009e\n\6\3\6\3\6\3"+
		"\6\3\6\3\6\3\6\3\6\7\6\u00a7\n\6\f\6\16\6\u00aa\13\6\3\6\3\6\3\6\3\6\3"+
		"\6\3\6\3\6\3\7\3\7\3\7\3\7\7\7\u00b7\n\7\f\7\16\7\u00ba\13\7\3\b\3\b\3"+
		"\b\3\b\3\b\3\b\3\b\3\b\3\b\3\b\3\b\3\b\3\b\3\b\3\b\5\b\u00cb\n\b\3\t\3"+
		"\t\3\t\3\t\3\t\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\5\n\u00dd\n"+
		"\n\3\13\3\13\3\13\3\13\3\13\3\13\3\13\3\f\3\f\3\f\3\f\3\f\3\f\3\r\3\r"+
		"\3\r\3\r\3\16\3\16\3\16\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\5\17\u00fb"+
		"\n\17\3\20\3\20\3\20\3\20\3\21\3\21\3\21\3\21\3\21\3\21\3\21\5\21\u0108"+
		"\n\21\3\22\3\22\3\22\3\22\3\23\3\23\3\23\3\23\3\23\3\23\3\23\5\23\u0115"+
		"\n\23\3\24\3\24\3\24\3\24\3\25\3\25\3\25\3\25\3\25\3\25\3\25\3\25\5\25"+
		"\u0123\n\25\3\26\3\26\3\26\3\26\3\27\3\27\3\27\3\27\3\27\3\27\3\27\3\27"+
		"\5\27\u0131\n\27\3\30\3\30\3\30\3\30\3\31\3\31\3\31\3\31\3\31\3\31\3\31"+
		"\3\31\5\31\u013f\n\31\3\32\3\32\3\32\3\32\3\33\3\33\3\33\3\33\3\33\3\33"+
		"\3\33\3\33\5\33\u014d\n\33\3\34\3\34\3\34\3\34\3\34\3\34\3\34\3\34\5\34"+
		"\u0157\n\34\3\35\3\35\3\35\3\35\3\36\3\36\3\36\3\36\3\36\3\36\5\36\u0163"+
		"\n\36\3\37\3\37\3\37\3\37\3 \3 \3 \3 \3 \3 \3 \3 \3 \3 \3 \3 \3 \7 \u0176"+
		"\n \f \16 \u0179\13 \3 \3 \3 \3 \5 \u017f\n \3 \3 \3 \3 \5 \u0185\n \3"+
		"!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3"+
		"!\3!\3!\3!\5!\u01a2\n!\3\"\3\"\3\"\3\"\3\"\3\"\3\"\3\"\3\"\3\"\5\"\u01ae"+
		"\n\"\3\"\2\2#\2\4\6\b\n\f\16\20\22\24\26\30\32\34\36 \"$&(*,.\60\62\64"+
		"\668:<>@B\2\7\3\2\31\32\3\2\33\34\3\2\35\36\3\2\37 \4\2\36\36!!\2\u01b4"+
		"\2D\3\2\2\2\4R\3\2\2\2\6e\3\2\2\2\b\u0080\3\2\2\2\n\u0087\3\2\2\2\f\u00b2"+
		"\3\2\2\2\16\u00ca\3\2\2\2\20\u00cc\3\2\2\2\22\u00d1\3\2\2\2\24\u00de\3"+
		"\2\2\2\26\u00e5\3\2\2\2\30\u00eb\3\2\2\2\32\u00ef\3\2\2\2\34\u00fa\3\2"+
		"\2\2\36\u00fc\3\2\2\2 \u0107\3\2\2\2\"\u0109\3\2\2\2$\u0114\3\2\2\2&\u0116"+
		"\3\2\2\2(\u0122\3\2\2\2*\u0124\3\2\2\2,\u0130\3\2\2\2.\u0132\3\2\2\2\60"+
		"\u013e\3\2\2\2\62\u0140\3\2\2\2\64\u014c\3\2\2\2\66\u0156\3\2\2\28\u0158"+
		"\3\2\2\2:\u0162\3\2\2\2<\u0164\3\2\2\2>\u0184\3\2\2\2@\u01a1\3\2\2\2B"+
		"\u01ad\3\2\2\2DE\b\2\1\2EF\5\4\3\2FL\b\2\1\2GH\5\6\4\2HI\b\2\1\2IK\3\2"+
		"\2\2JG\3\2\2\2KN\3\2\2\2LJ\3\2\2\2LM\3\2\2\2MO\3\2\2\2NL\3\2\2\2OP\7\2"+
		"\2\3PQ\b\2\1\2Q\3\3\2\2\2RS\7\3\2\2ST\7\60\2\2TU\b\3\1\2UV\7\4\2\2VW\7"+
		"\5\2\2WX\7\60\2\2XY\7\6\2\2YZ\7\7\2\2Z[\7\b\2\2[\\\b\3\1\2\\]\7\4\2\2"+
		"]^\5\f\7\2^_\7\t\2\2_`\5\32\16\2`a\7\n\2\2ab\7\13\2\2bc\7\13\2\2cd\b\3"+
		"\1\2d\5\3\2\2\2ef\7\3\2\2fg\7\60\2\2gk\b\4\1\2hi\7\f\2\2ij\7\60\2\2jl"+
		"\b\4\1\2kh\3\2\2\2kl\3\2\2\2lm\3\2\2\2ms\7\4\2\2no\5\b\5\2op\b\4\1\2p"+
		"r\3\2\2\2qn\3\2\2\2ru\3\2\2\2sq\3\2\2\2st\3\2\2\2t{\3\2\2\2us\3\2\2\2"+
		"vw\5\n\6\2wx\b\4\1\2xz\3\2\2\2yv\3\2\2\2z}\3\2\2\2{y\3\2\2\2{|\3\2\2\2"+
		"|~\3\2\2\2}{\3\2\2\2~\177\7\13\2\2\177\7\3\2\2\2\u0080\u0081\7\r\2\2\u0081"+
		"\u0082\7\60\2\2\u0082\u0083\7\7\2\2\u0083\u0084\5B\"\2\u0084\u0085\7\n"+
		"\2\2\u0085\u0086\b\5\1\2\u0086\t\3\2\2\2\u0087\u0088\7\5\2\2\u0088\u0089"+
		"\7\60\2\2\u0089\u009d\b\6\1\2\u008a\u009e\7\6\2\2\u008b\u008c\7\16\2\2"+
		"\u008c\u008d\7\60\2\2\u008d\u008e\7\7\2\2\u008e\u008f\5B\"\2\u008f\u0098"+
		"\b\6\1\2\u0090\u0091\7\17\2\2\u0091\u0092\7\60\2\2\u0092\u0093\7\7\2\2"+
		"\u0093\u0094\5B\"\2\u0094\u0095\b\6\1\2\u0095\u0097\3\2\2\2\u0096\u0090"+
		"\3\2\2\2\u0097\u009a\3\2\2\2\u0098\u0096\3\2\2\2\u0098\u0099\3\2\2\2\u0099"+
		"\u009b\3\2\2\2\u009a\u0098\3\2\2\2\u009b\u009c\7\20\2\2\u009c\u009e\3"+
		"\2\2\2\u009d\u008a\3\2\2\2\u009d\u008b\3\2\2\2\u009e\u009f\3\2\2\2\u009f"+
		"\u00a0\7\7\2\2\u00a0\u00a1\5B\"\2\u00a1\u00a2\b\6\1\2\u00a2\u00a8\7\4"+
		"\2\2\u00a3\u00a4\5\b\5\2\u00a4\u00a5\b\6\1\2\u00a5\u00a7\3\2\2\2\u00a6"+
		"\u00a3\3\2\2\2\u00a7\u00aa\3\2\2\2\u00a8\u00a6\3\2\2\2\u00a8\u00a9\3\2"+
		"\2\2\u00a9\u00ab\3\2\2\2\u00aa\u00a8\3\2\2\2\u00ab\u00ac\5\f\7\2\u00ac"+
		"\u00ad\7\t\2\2\u00ad\u00ae\5\32\16\2\u00ae\u00af\7\n\2\2\u00af\u00b0\7"+
		"\13\2\2\u00b0\u00b1\b\6\1\2\u00b1\13\3\2\2\2\u00b2\u00b8\b\7\1\2\u00b3"+
		"\u00b4\5\16\b\2\u00b4\u00b5\b\7\1\2\u00b5\u00b7\3\2\2\2\u00b6\u00b3\3"+
		"\2\2\2\u00b7\u00ba\3\2\2\2\u00b8\u00b6\3\2\2\2\u00b8\u00b9\3\2\2\2\u00b9"+
		"\r\3\2\2\2\u00ba\u00b8\3\2\2\2\u00bb\u00bc\5\20\t\2\u00bc\u00bd\b\b\1"+
		"\2\u00bd\u00cb\3\2\2\2\u00be\u00bf\5\22\n\2\u00bf\u00c0\b\b\1\2\u00c0"+
		"\u00cb\3\2\2\2\u00c1\u00c2\5\24\13\2\u00c2\u00c3\b\b\1\2\u00c3\u00cb\3"+
		"\2\2\2\u00c4\u00c5\5\26\f\2\u00c5\u00c6\b\b\1\2\u00c6\u00cb\3\2\2\2\u00c7"+
		"\u00c8\5\30\r\2\u00c8\u00c9\b\b\1\2\u00c9\u00cb\3\2\2\2\u00ca\u00bb\3"+
		"\2\2\2\u00ca\u00be\3\2\2\2\u00ca\u00c1\3\2\2\2\u00ca\u00c4\3\2\2\2\u00ca"+
		"\u00c7\3\2\2\2\u00cb\17\3\2\2\2\u00cc\u00cd\7\4\2\2\u00cd\u00ce\5\f\7"+
		"\2\u00ce\u00cf\7\13\2\2\u00cf\u00d0\b\t\1\2\u00d0\21\3\2\2\2\u00d1\u00d2"+
		"\7\21\2\2\u00d2\u00d3\7\16\2\2\u00d3\u00d4\5\32\16\2\u00d4\u00d5\7\20"+
		"\2\2\u00d5\u00d6\7\22\2\2\u00d6\u00d7\5\16\b\2\u00d7\u00dc\b\n\1\2\u00d8"+
		"\u00d9\7\23\2\2\u00d9\u00da\5\16\b\2\u00da\u00db\b\n\1\2\u00db\u00dd\3"+
		"\2\2\2\u00dc\u00d8\3\2\2\2\u00dc\u00dd\3\2\2\2\u00dd\23\3\2\2\2\u00de"+
		"\u00df\7\24\2\2\u00df\u00e0\7\16\2\2\u00e0\u00e1\5\32\16\2\u00e1\u00e2"+
		"\7\20\2\2\u00e2\u00e3\5\16\b\2\u00e3\u00e4\b\13\1\2\u00e4\25\3\2\2\2\u00e5"+
		"\u00e6\7\25\2\2\u00e6\u00e7\5\32\16\2\u00e7\u00e8\7\20\2\2\u00e8\u00e9"+
		"\7\n\2\2\u00e9\u00ea\b\f\1\2\u00ea\27\3\2\2\2\u00eb\u00ec\5\32\16\2\u00ec"+
		"\u00ed\7\n\2\2\u00ed\u00ee\b\r\1\2\u00ee\31\3\2\2\2\u00ef\u00f0\5\34\17"+
		"\2\u00f0\u00f1\b\16\1\2\u00f1\33\3\2\2\2\u00f2\u00f3\5\36\20\2\u00f3\u00f4"+
		"\7\26\2\2\u00f4\u00f5\5\34\17\2\u00f5\u00f6\b\17\1\2\u00f6\u00fb\3\2\2"+
		"\2\u00f7\u00f8\5\36\20\2\u00f8\u00f9\b\17\1\2\u00f9\u00fb\3\2\2\2\u00fa"+
		"\u00f2\3\2\2\2\u00fa\u00f7\3\2\2\2\u00fb\35\3\2\2\2\u00fc\u00fd\5\"\22"+
		"\2\u00fd\u00fe\5 \21\2\u00fe\u00ff\b\20\1\2\u00ff\37\3\2\2\2\u0100\u0101"+
		"\7\27\2\2\u0101\u0102\5\"\22\2\u0102\u0103\b\21\1\2\u0103\u0104\5 \21"+
		"\2\u0104\u0105\b\21\1\2\u0105\u0108\3\2\2\2\u0106\u0108\b\21\1\2\u0107"+
		"\u0100\3\2\2\2\u0107\u0106\3\2\2\2\u0108!\3\2\2\2\u0109\u010a\5&\24\2"+
		"\u010a\u010b\5$\23\2\u010b\u010c\b\22\1\2\u010c#\3\2\2\2\u010d\u010e\7"+
		"\30\2\2\u010e\u010f\5&\24\2\u010f\u0110\b\23\1\2\u0110\u0111\5$\23\2\u0111"+
		"\u0112\b\23\1\2\u0112\u0115\3\2\2\2\u0113\u0115\b\23\1\2\u0114\u010d\3"+
		"\2\2\2\u0114\u0113\3\2\2\2\u0115%\3\2\2\2\u0116\u0117\5*\26\2\u0117\u0118"+
		"\5(\25\2\u0118\u0119\b\24\1\2\u0119\'\3\2\2\2\u011a\u011b\t\2\2\2\u011b"+
		"\u011c\b\25\1\2\u011c\u011d\5*\26\2\u011d\u011e\b\25\1\2\u011e\u011f\5"+
		"(\25\2\u011f\u0120\b\25\1\2\u0120\u0123\3\2\2\2\u0121\u0123\b\25\1\2\u0122"+
		"\u011a\3\2\2\2\u0122\u0121\3\2\2\2\u0123)\3\2\2\2\u0124\u0125\5.\30\2"+
		"\u0125\u0126\5,\27\2\u0126\u0127\b\26\1\2\u0127+\3\2\2\2\u0128\u0129\t"+
		"\3\2\2\u0129\u012a\b\27\1\2\u012a\u012b\5.\30\2\u012b\u012c\b\27\1\2\u012c"+
		"\u012d\5,\27\2\u012d\u012e\b\27\1\2\u012e\u0131\3\2\2\2\u012f\u0131\b"+
		"\27\1\2\u0130\u0128\3\2\2\2\u0130\u012f\3\2\2\2\u0131-\3\2\2\2\u0132\u0133"+
		"\5\62\32\2\u0133\u0134\5\60\31\2\u0134\u0135\b\30\1\2\u0135/\3\2\2\2\u0136"+
		"\u0137\t\4\2\2\u0137\u0138\b\31\1\2\u0138\u0139\5\62\32\2\u0139\u013a"+
		"\b\31\1\2\u013a\u013b\5\60\31\2\u013b\u013c\b\31\1\2\u013c\u013f\3\2\2"+
		"\2\u013d\u013f\b\31\1\2\u013e\u0136\3\2\2\2\u013e\u013d\3\2\2\2\u013f"+
		"\61\3\2\2\2\u0140\u0141\5\66\34\2\u0141\u0142\5\64\33\2\u0142\u0143\b"+
		"\32\1\2\u0143\63\3\2\2\2\u0144\u0145\t\5\2\2\u0145\u0146\b\33\1\2\u0146"+
		"\u0147\5\66\34\2\u0147\u0148\b\33\1\2\u0148\u0149\5\64\33\2\u0149\u014a"+
		"\b\33\1\2\u014a\u014d\3\2\2\2\u014b\u014d\b\33\1\2\u014c\u0144\3\2\2\2"+
		"\u014c\u014b\3\2\2\2\u014d\65\3\2\2\2\u014e\u014f\t\6\2\2\u014f\u0150"+
		"\b\34\1\2\u0150\u0151\5\66\34\2\u0151\u0152\b\34\1\2\u0152\u0157\3\2\2"+
		"\2\u0153\u0154\58\35\2\u0154\u0155\b\34\1\2\u0155\u0157\3\2\2\2\u0156"+
		"\u014e\3\2\2\2\u0156\u0153\3\2\2\2\u0157\67\3\2\2\2\u0158\u0159\5<\37"+
		"\2\u0159\u015a\5:\36\2\u015a\u015b\b\35\1\2\u015b9\3\2\2\2\u015c\u015d"+
		"\7\"\2\2\u015d\u015e\5\32\16\2\u015e\u015f\7#\2\2\u015f\u0160\b\36\1\2"+
		"\u0160\u0163\3\2\2\2\u0161\u0163\b\36\1\2\u0162\u015c\3\2\2\2\u0162\u0161"+
		"\3\2\2\2\u0163;\3\2\2\2\u0164\u0165\5@!\2\u0165\u0166\5> \2\u0166\u0167"+
		"\b\37\1\2\u0167=\3\2\2\2\u0168\u017e\7$\2\2\u0169\u016a\7\60\2\2\u016a"+
		"\u016b\7\6\2\2\u016b\u017f\b \1\2\u016c\u016d\7\60\2\2\u016d\u016e\b "+
		"\1\2\u016e\u016f\7\16\2\2\u016f\u0170\5\32\16\2\u0170\u0177\b \1\2\u0171"+
		"\u0172\7\17\2\2\u0172\u0173\5\32\16\2\u0173\u0174\b \1\2\u0174\u0176\3"+
		"\2\2\2\u0175\u0171\3\2\2\2\u0176\u0179\3\2\2\2\u0177\u0175\3\2\2\2\u0177"+
		"\u0178\3\2\2\2\u0178\u017a\3\2\2\2\u0179\u0177\3\2\2\2\u017a\u017b\7\20"+
		"\2\2\u017b\u017f\3\2\2\2\u017c\u017d\7%\2\2\u017d\u017f\b \1\2\u017e\u0169"+
		"\3\2\2\2\u017e\u016c\3\2\2\2\u017e\u017c\3\2\2\2\u017f\u0180\3\2\2\2\u0180"+
		"\u0181\5> \2\u0181\u0182\b \1\2\u0182\u0185\3\2\2\2\u0183\u0185\b \1\2"+
		"\u0184\u0168\3\2\2\2\u0184\u0183\3\2\2\2\u0185?\3\2\2\2\u0186\u0187\7"+
		"-\2\2\u0187\u01a2\b!\1\2\u0188\u0189\7.\2\2\u0189\u01a2\b!\1\2\u018a\u018b"+
		"\7&\2\2\u018b\u018c\7\b\2\2\u018c\u018d\7\"\2\2\u018d\u018e\7-\2\2\u018e"+
		"\u018f\7#\2\2\u018f\u01a2\b!\1\2\u0190\u0191\7&\2\2\u0191\u0192\7\60\2"+
		"\2\u0192\u0193\7\6\2\2\u0193\u01a2\b!\1\2\u0194\u0195\7\'\2\2\u0195\u01a2"+
		"\b!\1\2\u0196\u0197\7(\2\2\u0197\u01a2\b!\1\2\u0198\u0199\7)\2\2\u0199"+
		"\u01a2\b!\1\2\u019a\u019b\7\60\2\2\u019b\u01a2\b!\1\2\u019c\u019d\7\16"+
		"\2\2\u019d\u019e\5\32\16\2\u019e\u019f\7\20\2\2\u019f\u01a0\b!\1\2\u01a0"+
		"\u01a2\3\2\2\2\u01a1\u0186\3\2\2\2\u01a1\u0188\3\2\2\2\u01a1\u018a\3\2"+
		"\2\2\u01a1\u0190\3\2\2\2\u01a1\u0194\3\2\2\2\u01a1\u0196\3\2\2\2\u01a1"+
		"\u0198\3\2\2\2\u01a1\u019a\3\2\2\2\u01a1\u019c\3\2\2\2\u01a2A\3\2\2\2"+
		"\u01a3\u01a4\7\b\2\2\u01a4\u01ae\b\"\1\2\u01a5\u01a6\7*\2\2\u01a6\u01ae"+
		"\b\"\1\2\u01a7\u01a8\7+\2\2\u01a8\u01ae\b\"\1\2\u01a9\u01aa\7,\2\2\u01aa"+
		"\u01ae\b\"\1\2\u01ab\u01ac\7\60\2\2\u01ac\u01ae\b\"\1\2\u01ad\u01a3\3"+
		"\2\2\2\u01ad\u01a5\3\2\2\2\u01ad\u01a7\3\2\2\2\u01ad\u01a9\3\2\2\2\u01ad"+
		"\u01ab\3\2\2\2\u01aeC\3\2\2\2\32Lks{\u0098\u009d\u00a8\u00b8\u00ca\u00dc"+
		"\u00fa\u0107\u0114\u0122\u0130\u013e\u014c\u0156\u0162\u0177\u017e\u0184"+
		"\u01a1\u01ad";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}