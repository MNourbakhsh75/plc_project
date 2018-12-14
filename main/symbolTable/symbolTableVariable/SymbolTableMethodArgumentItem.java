package main.symbolTable.symbolTableVariable;

import main.ast.Type.Type;
import main.ast.node.declaration.VarDeclaration;


public class SymbolTableMethodArgumentItem extends SymbolTableVariableItemBase {
    public SymbolTableMethodArgumentItem(String name , Type type , int index )
    {
        super( name , type , index );
    }
    public SymbolTableMethodArgumentItem(VarDeclaration argDeclaration )
    {
        super( argDeclaration );
    }
}
