grammar Smoola;
    @header
    {
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
    }
    @members
    {
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
    }
    program returns[ Program returnedProgram ] locals[ Program myProgram ]:
        {
            $myProgram = new Program();
        }
        myClass=mainClass {
            $myProgram.setMainClass( $myClass.mainClassDeclaration );
        }
        (otherClass=classDeclaration
        {
            $myProgram.addClass( $otherClass.myClassDeclaration );
        }
        )* EOF
        {
            ClassDeclaration objectClass = constructObjectClass();
            $returnedProgram = $myProgram;
        }
    ;
    mainClass returns[ ClassDeclaration mainClassDeclaration ] locals[ MethodDeclaration mainMethodDec ]:
        // name should be checked later
        'class' className=ID
        {
            $mainClassDeclaration = new ClassDeclaration( new Identifier( $className.text ) , null );
            setPosition( $mainClassDeclaration.getName() , $className.getLine() , $className.getCharPositionInLine() );

        }
        '{' 'def' mainMethod=ID '()' ':' 'int'
        {
            $mainMethodDec = new MainMethodDeclaration( new Identifier( $mainMethod.text ) ) ;
            $mainMethodDec.setActualReturnType( new IntType() );
            setPosition( $mainMethodDec.getName() , $mainMethod.getLine() , $mainMethod.getCharPositionInLine() );
        }
        '{'  stats=statements 'return' retExpr=expression ';' '}' '}'
        {
            $mainMethodDec.setReturnValue( $retExpr.finalExpr );
            for( Statement stat: $stats.myStatements )
            {
               $mainMethodDec.addStatement( stat );
            }
            $mainClassDeclaration.addMethodDeclaration( $mainMethodDec );
        }
    ;
    classDeclaration returns[ ClassDeclaration myClassDeclaration ] :
        'class' className=ID
        {
            $myClassDeclaration = new ClassDeclaration( new Identifier( $className.text ) , null );
            setPosition( $myClassDeclaration.getName() , $className.getLine() , $className.getCharPositionInLine() );

        }
        ('extends' parentClassName=ID
        {
            $myClassDeclaration.setParentName( new Identifier( $parentClassName.text ) );
            setPosition( $myClassDeclaration.getParentName() , $parentClassName.getLine() , $parentClassName.getCharPositionInLine() );
        }
        )? '{' (
            curVarDec=varDeclaration
            {
                $myClassDeclaration.addVarDeclaration( $curVarDec.returnedVarDeclaration );
            }
        )* (methodDec=methodDeclaration
        {
            $myClassDeclaration.addMethodDeclaration( $methodDec.methodDec );
        })* '}'
    ;
    varDeclaration returns[ VarDeclaration returnedVarDeclaration ]:
        'var' varName=ID ':' returnedType=type ';'
        {
            $returnedVarDeclaration = new VarDeclaration( new Identifier( $varName.text ) , $returnedType.returnedType );
            setPosition( $returnedVarDeclaration.getIdentifier() , $varName.getLine() , $varName.getCharPositionInLine() );
        }
    ;
    methodDeclaration returns[ MethodDeclaration methodDec ] locals[ VarDeclaration argDec ]:
        'def' methodName=ID
        {
            $methodDec = new MethodDeclaration( new Identifier( $methodName.text ) );
            setPosition( $methodDec.getName() , $methodName.getLine() , $methodName.getCharPositionInLine() );
        }
        ('()' | ('(' firstArgName=ID ':' firstArgType=type
        {
            $argDec = new VarDeclaration( new Identifier( $firstArgName.text ) , $firstArgType.returnedType );
            setPosition( $argDec.getIdentifier() , $firstArgName.getLine() , $firstArgName.getCharPositionInLine() );
            $methodDec.addArg( $argDec );
        }
        (',' otherArgName=ID ':' otherArgType=type
        {
            $argDec = new VarDeclaration( new Identifier( $otherArgName.text ) , $otherArgType.returnedType );
            setPosition( $argDec.getIdentifier() , $otherArgName.getLine() , $otherArgName.getCharPositionInLine() );
            $methodDec.addArg( $argDec );
        })* ')')) ':' actualReturnType=type
        {
            $methodDec.setActualReturnType( $actualReturnType.returnedType );
        }
        '{'  (
                localVar=varDeclaration
                {
                    $methodDec.addLocalVar( $localVar.returnedVarDeclaration );
                }
            )* stats=statements 'return' retExpr=expression ';' '}'
            {
                $methodDec.setReturnValue( $retExpr.finalExpr );
                for( Statement stat: $stats.myStatements )
                {
                    $methodDec.addStatement( stat );
                }
            }
    ;
    statements returns[ ArrayList<Statement> myStatements ]:
        {
             $myStatements = new ArrayList<>();
        }
        (
            stat=statement
            {
                if( $stat.myStatement != null )
                    $myStatements.add( $stat.myStatement );
            }
        )*
    ;
    statement returns[ Statement myStatement ]:
        seenBlock=statementBlock
        {
            $myStatement = $seenBlock.block;
        }
        |
        conditionalStat=statementCondition
        {
            $myStatement = $conditionalStat.conditionStat;
        }|
        whileStat=statementLoop
        {
            $myStatement = $whileStat.whileStat;
        }|
        writeStat=statementWrite
         {
            $myStatement = $writeStat.writeStat;
         }|
        assignStat=statementAssignment
        {
            $myStatement = $assignStat.assignStat;
        }
    ;
    statementBlock returns[ Block block ]:
        '{'  blockStatements=statements '}'
        {
            $block = new Block();
            for( Statement myStatement: $blockStatements.myStatements )
                $block.addStatement( myStatement );
        }
    ;
    statementCondition returns[ Conditional conditionStat ]:
        'if' '('condition=expression')' 'then' consequenceStat=statement {
            $conditionStat = new Conditional( $condition.finalExpr , $consequenceStat.myStatement );
        } ('else' altStat=statement
           {
              $conditionStat.setAlternativeBody( $altStat.myStatement );
           }
        )?
    ;
    statementLoop returns[ While whileStat ]:
        'while' '(' loopCondition=expression ')' stat=statement
        {
            $whileStat = new While( $loopCondition.finalExpr , $stat.myStatement );
        }
    ;
    statementWrite returns[ Write writeStat ]:
        'writeln(' writeExpr=expression ')' ';'
        {
            $writeStat = new Write( $writeExpr.finalExpr );
        }
    ;
    statementAssignment returns[ Assign assignStat ]:
        expr=expression ';'
        {
            $assignStat = new Assign( null , null );
            if( $expr.finalExpr instanceof BinaryExpression && ( ( BinaryExpression ) $expr.finalExpr).getBinaryOperator().equals( BinaryOperator.assign )  )
            {
                BinaryExpression bExpr = ( BinaryExpression ) $expr.finalExpr;
                $assignStat.setrValue( bExpr.getRight() );
                $assignStat.setlValue( bExpr.getLeft() );
            }
            else
            {
                $assignStat.setlValue( $expr.finalExpr );
                $assignStat.setrValue( null );
            }
            setPosition( $assignStat , $expr.finalExpr.getLineNum() , $expr.finalExpr.getColNum() );
        }
    ;

    expression returns[ Expression finalExpr ]:
		exprAssign=expressionAssignment
		{
		    $finalExpr = $exprAssign.assignRetExpr;
		}
	;

    expressionAssignment returns[ Expression assignRetExpr ]:
		lOrExpr=expressionOr assign='=' rAssignExpr=expressionAssignment
		{
		    $assignRetExpr = new BinaryExpression( $lOrExpr.orExpr , $rAssignExpr.assignRetExpr, BinaryOperator.assign );
		    setPosition( $assignRetExpr , $assign.getLine() , $assign.getCharPositionInLine() );
		}
	    |	singleOrExpr=expressionOr
	    {
	        $assignRetExpr = $singleOrExpr.orExpr;
	    }
	;

    expressionOr returns[ Expression orExpr ]:
		andExpr=expressionAnd
		finalOrExpr=expressionOrTemp[ $andExpr.andExpr ]
		{
		    $orExpr = $finalOrExpr.multipleOrExpr;
		}
	;

    expressionOrTemp[ Expression orExpr ] returns[ Expression multipleOrExpr ] locals[ BinaryExpression realOrExpr ]:
        (
		orOp='||' andExpr=expressionAnd
		{
		    $realOrExpr = new BinaryExpression( $orExpr , $andExpr.andExpr , BinaryOperator.or );
		    setPosition( $realOrExpr , $orOp.getLine() , $orOp.getCharPositionInLine() );
		}
		retMultipleOrExpr=expressionOrTemp[ $realOrExpr ]
		{
		    $multipleOrExpr = $retMultipleOrExpr.multipleOrExpr;
		}
	    |
	    {
            $multipleOrExpr = $orExpr;
	    }
	    )
	;

    expressionAnd returns[ Expression andExpr ]:
		eqExpr=expressionEq
		retMultipleAndExpr=expressionAndTemp[ $eqExpr.eqExpr ]
		{
		    $andExpr = $retMultipleAndExpr.multipleAndExpr;
		}
	;

    expressionAndTemp[ Expression andExpr ] returns[ Expression multipleAndExpr ] locals[ BinaryExpression realAndExpr ]: //this rule is incomplete
		andOp='&&' eqExpr=expressionEq
		{
            $realAndExpr = new BinaryExpression( $andExpr , $eqExpr.eqExpr , BinaryOperator.and );
            setPosition( $realAndExpr , $andOp.getLine() , $andOp.getCharPositionInLine() );

		}
		retMultipleAndExpr=expressionAndTemp[ $realAndExpr ]
		{
		    $multipleAndExpr = $retMultipleAndExpr.multipleAndExpr;
		}
	    |
	    {
            $multipleAndExpr = $andExpr;
	    }
	;

    expressionEq returns[ Expression eqExpr ]:
		compExpr=expressionCmp multipleEqExpr=expressionEqTemp[ $compExpr.compExpr ]
		{
		    $eqExpr = $multipleEqExpr.retMultipleEqExpr;
		}
	;

    expressionEqTemp[ Expression eqExpr ] returns[ Expression retMultipleEqExpr ] locals[ BinaryExpression realEqExpr , BinaryOperator eqBinOp ]:
		eqOp=('=='
		|
		'<>' )

		{
		    if( $eqOp.text.equals( "==" ) )
		        $eqBinOp = BinaryOperator.eq;
		    else if( $eqOp.text.equals( "<>" ) )
		        $eqBinOp = BinaryOperator.neq;
		}
		 compExpr=expressionCmp
		 {
		    $realEqExpr = new BinaryExpression( $eqExpr , $compExpr.compExpr , $eqBinOp );
            setPosition( $realEqExpr , $eqOp.getLine() , $eqOp.getCharPositionInLine() );

		 }
		 multipleEqExpr=expressionEqTemp[ $realEqExpr ]
		 {
		    $retMultipleEqExpr = $multipleEqExpr.retMultipleEqExpr;
		 }
	    |
	    {
	        $retMultipleEqExpr = $eqExpr;
	    }
	;

    expressionCmp returns[ Expression compExpr ]:
		addExpr=expressionAdd retMultipleCompExpr=expressionCmpTemp[ $addExpr.addExpr ]
		{
		    $compExpr = $retMultipleCompExpr.retMultipleCompExpr;
		}
	;

    expressionCmpTemp[ Expression compExpr ] returns[ Expression retMultipleCompExpr ] locals[ BinaryExpression realCompExpr , BinaryOperator compBinOp ]:
		    relatOp= (
		    '<'
		    |
		    '>'
		    )
		     {
		        if( $relatOp.text.equals( ">" ) )
		        {
		            $compBinOp = BinaryOperator.gt;
		        }
		        else if( $relatOp.text.equals( "<" ) )
		        {
		            $compBinOp = BinaryOperator.lt;
		        }
		     }addExpr=expressionAdd
		    {
		        $realCompExpr = new BinaryExpression( $compExpr , $addExpr.addExpr , $compBinOp );
                setPosition( $realCompExpr , $relatOp.getLine() , $relatOp.getCharPositionInLine() );

		    }
		    multipleCompExpr=expressionCmpTemp[ $realCompExpr ]
		    {
		        $retMultipleCompExpr = $multipleCompExpr.retMultipleCompExpr;
		    }
            |
            {
                $retMultipleCompExpr = $compExpr;
            }
	;

    expressionAdd returns[ Expression addExpr ]:
		multExpr=expressionMult multipleAddExpr=expressionAddTemp[ $multExpr.multExpr ]
		{
		    $addExpr = $multipleAddExpr.retMultipleAddExpr;
		}
	;

    expressionAddTemp[ Expression addExpr ] returns[ Expression retMultipleAddExpr ] locals[ BinaryExpression realAddExpr , BinaryOperator addBinOp ]:

		    addOp=('+'
		    |
		    '-' )
		    {
		        if( $addOp.text.equals( "+" ) )
		            $addBinOp = BinaryOperator.add;
		        else if( $addOp.text.equals( "-" ) )
		            $addBinOp = BinaryOperator.sub;
		    }
		    multExpr=expressionMult
		{
		    $realAddExpr = new BinaryExpression( $addExpr , $multExpr.multExpr , $addBinOp );
            setPosition( $realAddExpr , $addOp.getLine() , $addOp.getCharPositionInLine() );
		}
		multipleAddExpr=expressionAddTemp[ $realAddExpr ]
		{
		    $retMultipleAddExpr = $multipleAddExpr.retMultipleAddExpr;
		}
	    |
	    {
	        $retMultipleAddExpr = $addExpr;
	    }
	;

    expressionMult returns[ Expression multExpr ]:
		unaryExpr=expressionUnary retMultipleMultExpr=expressionMultTemp[ $unaryExpr.unaryExpr ]
		{
		    $multExpr = $retMultipleMultExpr.retMultipleMultExpr;
		}
	;

    expressionMultTemp[ Expression multExpr ] returns[ Expression retMultipleMultExpr ] locals[ BinaryOperator multBinOp , BinaryExpression realMultExpr ]:
		multOp=('*'
        		    |
        		    '/' )
        		    {
        		        if( $multOp.text.equals( "*" ) )
        		            $multBinOp = BinaryOperator.mult;
        		        else if( $multOp.text.equals( "/" ) )
        		            $multBinOp = BinaryOperator.div;
        		    }
		unaryExpr=expressionUnary
		{
		    $realMultExpr = new BinaryExpression( $multExpr , $unaryExpr.unaryExpr , $multBinOp );
            setPosition( $realMultExpr , $multOp.getLine() , $multOp.getCharPositionInLine() );
		}
		multipleMultExpr=expressionMultTemp[ $realMultExpr ]
		{
		    $retMultipleMultExpr = $multipleMultExpr.retMultipleMultExpr;
		}
	    |
	    {
	        $retMultipleMultExpr = $multExpr;
	    }
	;

    expressionUnary returns[ Expression unaryExpr ] locals[ UnaryOperator uOp ]:
		(
            notOp=(
                '!'
                |
                '-'
            )
            {
                if( $notOp.text.equals( "!" ) )
                    $uOp = UnaryOperator.not;
                else if( $notOp.text.equals( "-" ) )
                    $uOp = UnaryOperator.minus;
            }
            unaryOperand=expressionUnary
            {
                $unaryExpr = new UnaryExpression( $uOp , $unaryOperand.unaryExpr );
                setPosition( $unaryExpr , $notOp.getLine() , $notOp.getCharPositionInLine() );
            }
            |
            memExpr=expressionMem
            {
                $unaryExpr = $memExpr.memExpr;
            }
	    )
	;

    expressionMem returns[ Expression memExpr ]:
		methodExpr=expressionMethods arrExpr=expressionMemTemp[ $methodExpr.methodExpr ]
		{
		    $memExpr = $arrExpr.realArrExpr;
		}
	;

    expressionMemTemp[ Expression arrExpr ] returns[ Expression realArrExpr ]:
		'[' subscript=expression ']'
		{
            $realArrExpr = new ArrayCall( $arrExpr , $subscript.finalExpr );
            setPosition( $realArrExpr , $arrExpr.getLineNum() , $arrExpr.getColNum() );
		}
	    |
	    {
            $realArrExpr = $arrExpr;
	    }
	;
	expressionMethods returns[ Expression methodExpr ]:
	    otherExpr=expressionOther retMethodExpr=expressionMethodsTemp[ $otherExpr.otherExpr ]
	    {
	        $methodExpr = $retMethodExpr.realMethodCallExpr;
	    }
	;
	expressionMethodsTemp[ Expression instance ] returns[ Expression realMethodCallExpr ] locals[ Expression methodCallExpr ]:
	    '.' (
	    methodName=ID '()'
	    {
	        $methodCallExpr = new MethodCall( $instance , new Identifier( $methodName.text ) );
            setPosition( ( ( MethodCall ) $methodCallExpr ).getMethodName() , $methodName.getLine() , $methodName.getCharPositionInLine() );

	    }
	    |
	    methodName=ID
	    {
	        $methodCallExpr = new MethodCall( $instance , new Identifier( $methodName.text ) );
	        setPosition( ( ( MethodCall ) $methodCallExpr ).getMethodName() , $methodName.getLine() , $methodName.getCharPositionInLine() );
	    }
	    '(' (argExpr=expression
	    {
	        ( ( MethodCall ) $methodCallExpr ).addArg( $argExpr.finalExpr );
	    }
	    (',' argExpr=expression
	    {
	        ( ( MethodCall ) $methodCallExpr ).addArg( $argExpr.finalExpr );
	    }
	    )*) ')'
	    |
	    'length'
	    {
	        $methodCallExpr = new Length( $instance );
	    }
	    ) retMethodCallExpr=expressionMethodsTemp[ $methodCallExpr ]
	    {
	        $realMethodCallExpr = $retMethodCallExpr.realMethodCallExpr;
	    }
	    |
	    {
	        $realMethodCallExpr = $instance;
	    }
	;
    expressionOther returns[ Expression otherExpr ]:
        (
		number=CONST_NUM
		{
            $otherExpr = new IntValue( $number.int , new IntType() );
           setPosition( $otherExpr , $number.getLine() , $number.getCharPositionInLine() );

        }
        )
        |	( string=CONST_STR
        {
            $otherExpr = new StringValue( $string.text , new StringType() );
            setPosition( $otherExpr , $string.getLine() , $string.getCharPositionInLine() );

        }
        )
        |
        (
        newExpr='new ' 'int' '[' arraySize=CONST_NUM ']'
        {
            $otherExpr = new NewArray();
            ( ( NewArray ) $otherExpr ).setExpression( new IntValue( $arraySize.int , new IntType() ) );
            setPosition( $otherExpr , $newExpr.getLine() , $newExpr.getCharPositionInLine() );
            setPosition( ( ( NewArray ) $otherExpr ).getExpression() , $arraySize.getLine() , $arraySize.getCharPositionInLine() );

        }
        )
        |
        (
        newExpr='new ' className=ID '()'
        {
            $otherExpr = new NewClass( new Identifier( $className.text ) );
            Identifier newClassName = ( ( NewClass ) $otherExpr ).getClassName();
            setPosition( newClassName , $className.getLine()  , $className.getCharPositionInLine() );
            setPosition( $otherExpr , $newExpr.getLine()  , $newExpr.getCharPositionInLine() );

        }
        )
        |
        (
        thisExpr='this'
        {
            $otherExpr = new This();
            setPosition( $otherExpr , $thisExpr.getLine()  , $thisExpr.getCharPositionInLine() );

        }
        )
        |
        (
        trueExpr='true'
        {
            $otherExpr = new BooleanValue( true , new BooleanType() );
            setPosition( $otherExpr , $trueExpr.getLine()  , $trueExpr.getCharPositionInLine() );
        }
        )
        |
        (
        falseExpr='false'
        {
            $otherExpr = new BooleanValue( false , new BooleanType() );
            setPosition( $otherExpr , $falseExpr.getLine()  , $falseExpr.getCharPositionInLine() );

        }
        )
        |
        (
        id=ID
        {
            $otherExpr = new Identifier( $id.text );
            setPosition( $otherExpr , $id.getLine() , $id.getCharPositionInLine() );
        }
        )
        |
        (
        leftPara='(' paraExpr=expression ')'
        {
            $otherExpr = $paraExpr.finalExpr;
            setPosition( $otherExpr , $leftPara.getLine() , $leftPara.getCharPositionInLine() );
        }
        )
	;
	type returns[ Type returnedType ]:
	    'int' { $returnedType = new IntType(); } |
	    'boolean' { $returnedType = new BooleanType(); } |
	    'string' { $returnedType = new StringType(); } |
	    'int[]' { $returnedType = new ArrayType(); } |
	    classType=ID {
	        $returnedType = new UserDefinedType();
	        ( ( UserDefinedType ) $returnedType).setName( new Identifier( $classType.text ) );
	        setPosition( $returnedType , $classType.getLine() , $classType.getCharPositionInLine() );
	    }
	;
    CONST_NUM:
		[0-9]+
	;

    CONST_STR:
		'"' ~('\r' | '\n' | '"')* '"'
	;
    NL:
		'\r'? '\n' -> skip
	;

    ID:
		[a-zA-Z_][a-zA-Z0-9_]*
	;

    COMMENT:
		'#'(~[\r\n])* -> skip
	;


    WS:
    	[ \t] -> skip
    ;