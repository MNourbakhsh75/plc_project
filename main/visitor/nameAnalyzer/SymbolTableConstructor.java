package main.visitor.nameAnalyzer;

import main.ast.node.Program;
import main.ast.node.declaration.ClassDeclaration;
import main.ast.node.declaration.MethodDeclaration;
import main.ast.node.declaration.VarDeclaration;
import main.symbolTable.ClassSymbolTableItem;
import main.symbolTable.itemException.ItemAlreadyExistsException;
import main.symbolTable.SymbolTable;
import main.symbolTable.SymbolTableMethodItem;
import main.symbolTable.symbolTableVariable.SymbolTableFieldVariableItem;
import main.symbolTable.symbolTableVariable.SymbolTableLocalVariableItem;
import main.symbolTable.symbolTableVariable.SymbolTableMethodArgumentItem;



public class SymbolTableConstructor {
    public void constructProgramSym()
    {
        SymbolTable.push( new SymbolTable( null) );
        SymbolTable.root = SymbolTable.top;
    }
    public void construct(ClassDeclaration classDeclaration )
    {
        SymbolTable classSymTable = new SymbolTable( SymbolTable.top );
        ClassSymbolTableItem classItem = new ClassSymbolTableItem( classDeclaration );
        try {
            classItem.setSymbolTable( classSymTable );
            SymbolTable.root.put(classItem);
        }
        catch( ItemAlreadyExistsException itemDuplication )
        {
            String className = SymbolTable.root.getItemCount() + "$" + classDeclaration.getName().getName();
            classItem.setName( className );
            try {
                SymbolTable.root.put(classItem);
            }
            catch( ItemAlreadyExistsException errorItemDuplication )
            {
                System.out.println( "an error occurred" );
            }
        }
        SymbolTable.push( classSymTable );
        addFieldsToSymTable( classDeclaration );
    }
    public void addFieldsToSymTable( ClassDeclaration classDeclaration )
    {
        for(VarDeclaration field: classDeclaration.getVarDeclarations() )
        {
            SymbolTableFieldVariableItem fieldItem = new SymbolTableFieldVariableItem( field );
            try
            {
                SymbolTable.top.put( fieldItem );
            }
            catch( ItemAlreadyExistsException fieldDuplication )
            {
                try
                {
                    String newName =  SymbolTable.top.getItemCount() + "$" + field.getIdentifier().getName();
                    fieldItem.setName( newName );
                    SymbolTable.top.put( fieldItem );
                }
                catch( ItemAlreadyExistsException errorFieldDuplication )
                {
                    System.out.println( "error occurred in adding variable to symbol table" );
                }
            }
        }
    }
    public void addMethodArgsToSymTable( MethodDeclaration methodDeclaration )
    {
        for( VarDeclaration arg: methodDeclaration.getArgs() )
        {
            SymbolTableMethodArgumentItem methodArg = new SymbolTableMethodArgumentItem( arg );
            try
            {
                SymbolTable.top.put( methodArg );
            }
            catch( ItemAlreadyExistsException argDuplication )
            {
                try
                {
                    String newArgName = SymbolTable.top.getItemCount() + "$" + arg.getIdentifier().getName();
                    methodArg.setName( newArgName );
                    SymbolTable.top.put( methodArg );
                }
                catch( ItemAlreadyExistsException errArgDuplication )
                {
                    System.out.println( "there is an error occurred when adding argument variable" );
                }
            }
        }
    }
    public void addLocalVarToSymTable( MethodDeclaration methodDeclaration )
    {
        for( VarDeclaration localVar: methodDeclaration.getLocalVars() )
        {
            SymbolTableLocalVariableItem methodLocalVar = new SymbolTableLocalVariableItem( localVar );
            try
            {
                SymbolTable.top.put( methodLocalVar );
            }
            catch( ItemAlreadyExistsException localVarDuplication )
            {
                try
                {
                    String newVarName =  SymbolTable.top.getItemCount() + "$" + localVar.getIdentifier().getName();
                    methodLocalVar.setName( newVarName );
                    SymbolTable.top.put( methodLocalVar );
                }
                catch( ItemAlreadyExistsException errArgDuplication )
                {
                    System.out.println( "there is an error occurred when adding local variable" );
                }
            }
        }
    }
    public void construct( MethodDeclaration methodDeclaration )
    {
        SymbolTableMethodItem methodItem = new SymbolTableMethodItem( methodDeclaration );
        methodItem.setMethodDeclaration( methodDeclaration );
        SymbolTable methodSymbolTable = new SymbolTable( SymbolTable.top );
        try
        {
            SymbolTable.top.put( methodItem );
        }
        catch( ItemAlreadyExistsException methodDuplication )
        {
            String newMethodName =  SymbolTable.top.getItemCount() + "$" + methodDeclaration.getName().getName();
            methodItem.setName( newMethodName );
            try
            {
                SymbolTable.top.put( methodItem );
            }
            catch( ItemAlreadyExistsException errorMethodDuplication )
            {
                System.out.println( "an error occurred in adding method to symbol table" );
            }
        }
        methodItem.setMethodSymbolTable( methodSymbolTable );
        SymbolTable.push( methodSymbolTable );
        addMethodArgsToSymTable( methodDeclaration );
        addLocalVarToSymTable( methodDeclaration );
    }

}
