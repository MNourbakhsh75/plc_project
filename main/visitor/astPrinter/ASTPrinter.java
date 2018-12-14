package main.visitor.astPrinter;



import main.ast.node.Node;
import main.ast.node.Program;
import main.ast.node.declaration.ClassDeclaration;
import main.ast.node.declaration.MainMethodDeclaration;
import main.ast.node.declaration.MethodDeclaration;
import main.ast.node.declaration.VarDeclaration;
import main.ast.node.expression.*;
import main.ast.node.expression.Value.BooleanValue;
import main.ast.node.expression.Value.IntValue;
import main.ast.node.expression.Value.StringValue;
import main.ast.node.statement.*;
import main.visitor.VisitorImpl;


public class ASTPrinter extends VisitorImpl {
    @Override
    public void visit(Node node) {
        //TODO: implement appropriate visit functionality
    }

    @Override
    public void visit(Program program){
        //TODO: implement appropriate visit functionality
        if( program == null )
            return;
        System.out.println(program.toString());
        this.visit(program.getMainClass());
        for (ClassDeclaration classDeclaration : program.getClasses())
            this.visit(classDeclaration);
    }

    @Override
    public void visit(ClassDeclaration classDeclaration) {
        //TODO: implement appropriate visit functionality
        if( classDeclaration == null )
            return;
        System.out.println( classDeclaration.toString() );
        visitExpr( classDeclaration.getName() );
        visitExpr( classDeclaration.getParentName() );
        for( VarDeclaration varDeclaration: classDeclaration.getVarDeclarations() )
            this.visit( varDeclaration );
        for( MethodDeclaration methodDeclaration: classDeclaration.getMethodDeclarations() )
            this.visit( methodDeclaration );
    }

    @Override
    public void visit(MethodDeclaration methodDeclaration) {
        //TODO: implement appropriate visit functionality
        if( methodDeclaration == null )
            return;
        System.out.println(methodDeclaration.toString());
        visitExpr( methodDeclaration.getName() );
        for( VarDeclaration argDeclaration: methodDeclaration.getArgs() )
            visit( argDeclaration );
        for( VarDeclaration localVariable: methodDeclaration.getLocalVars() )
            this.visit( localVariable );
        for( Statement statement : methodDeclaration.getBody() )
            visitStatement( statement );
        visitExpr( methodDeclaration.getReturnValue() );
    }

    @Override
    public void visit(MainMethodDeclaration mainMethodDeclaration) {
        //TODO: implement appropriate visit functionality
        if( mainMethodDeclaration == null )
            return;
        System.out.println(mainMethodDeclaration.toString());
        visitExpr( mainMethodDeclaration.getName() );
        for( Statement statement : mainMethodDeclaration.getBody() )
            visitStatement( statement );
        visitExpr( mainMethodDeclaration.getReturnValue() );
    }

    @Override
    public void visit(VarDeclaration varDeclaration) {
        //TODO: implement appropriate visit functionality
        if( varDeclaration == null )
            return;
        System.out.println(varDeclaration.toString());
        visitExpr( varDeclaration.getIdentifier() );
    }

    @Override
    public void visit(ArrayCall arrayCall) {
        //TODO: implement appropriate visit functionality
        if( arrayCall == null )
            return;
        System.out.println(arrayCall.toString());
        visitExpr( arrayCall.getInstance() );
        visitExpr( arrayCall.getIndex() );
    }

    @Override
    public void visit(BinaryExpression binaryExpression) {
        //TODO: implement appropriate visit functionality
        if( binaryExpression == null )
            return;
        Expression lOperand = binaryExpression.getLeft();
        Expression rOperand = binaryExpression.getRight();
        System.out.println( binaryExpression.toString() );
        visitExpr(lOperand);
        visitExpr(rOperand);
    }

    @Override
    public void visit(Identifier identifier) {
        //TODO: implement appropriate visit functionality
        if( identifier == null )
            return;
        System.out.println( identifier.toString() );
    }

    @Override
    public void visit(Length length) {
        //TODO: implement appropriate visit functionality
        if( length == null )
            return;
        System.out.println( length.toString() );
        visitExpr( length.getExpression() );
    }

    @Override
    public void visit(MethodCall methodCall) {
        if( methodCall == null )
            return;
        System.out.println( methodCall.toString() );
        visitExpr(methodCall.getInstance());
        visitExpr(methodCall.getMethodName());
        for (Expression argument : methodCall.getArgs())
            visitExpr(argument);
        //TODO: implement appropriate visit functionality
    }

    @Override
    public void visit(NewArray newArray) {
        //TODO: implement appropriate visit functionality
        if( newArray == null )
            return;
        System.out.println( newArray.toString() );
        visitExpr( newArray.getExpression() );
    }

    @Override
    public void visit(NewClass newClass) {
        //TODO: implement appropriate visit functionality
        if( newClass == null )
            return;
        System.out.println( newClass.toString() );
        visitExpr( newClass.getClassName() );
    }

    @Override
    public void visit(This instance) {
        //TODO: implement appropriate visit functionality
        if( instance == null )
            return;
        System.out.println( instance.toString() );
    }

    @Override
    public void visit(UnaryExpression unaryExpression) {
        //TODO: implement appropriate visit functionality
        if( unaryExpression == null )
            return;
            System.out.println( unaryExpression.toString() );
        try {
            visitExpr(unaryExpression.getValue());
        }
        catch( NullPointerException npe )
        {
            System.out.println( "unary value is null" );
        }
    }

    @Override
    public void visit(BooleanValue value) {
        //TODO: implement appropriate visit functionality
        if( value == null )
            return;
        System.out.println( value.toString() );
    }

    @Override
    public void visit(IntValue value) {
        //TODO: implement appropriate visit functionality
        if( value == null )
            return;
        System.out.println(value.toString());
    }

    @Override
    public void visit(StringValue value) {
        //TODO: implement appropriate visit functionality
        if( value == null )
            return;
        System.out.println( value.toString() );
    }

    @Override
    public void visit(Assign assign) {
        //TODO: implement appropriate visit functionality
        if( assign == null )
            return;
        System.out.println( assign.toString() );
        Expression lExpr = assign.getlValue();
        visitExpr(lExpr);
        Expression rValExpr = assign.getrValue();
        if (rValExpr != null)
            visitExpr(rValExpr);

    }

    @Override
    public void visit(Block block) {
        //TODO: implement appropriate visit functionality
        if( block == null )
            return;
        System.out.println( block.toString() );
        for( Statement blockStat : block.getBody() )
            this.visitStatement( blockStat );
    }

    @Override
    public void visit(Conditional conditional) {
        //TODO: implement appropriate visit functionality
        if( conditional == null )
            return;
        System.out.println( conditional.toString() );
        visitExpr( conditional.getExpression() );
        visitStatement( conditional.getConsequenceBody() );
        visitStatement( conditional.getAlternativeBody() );
    }

    @Override
    public void visit(While loop) {
        //TODO: implement appropriate visit functionality
        if( loop == null )
            return;
        System.out.println( loop.toString() );
        visitExpr( loop.getCondition() );
        visitStatement( loop.getBody() );

    }

    @Override
    public void visit(Write write) {
        //TODO: implement appropriate visit functionality
        if( write == null )
            return;
        System.out.println( write.toString() );
        visitExpr( write.getArg() );
    }
}

