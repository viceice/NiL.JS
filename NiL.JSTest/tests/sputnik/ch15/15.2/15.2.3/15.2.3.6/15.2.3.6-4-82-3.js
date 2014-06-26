/// Copyright (c) 2012 Ecma International.  All rights reserved. 
/**
 * @path ch15/15.2/15.2.3/15.2.3.6/15.2.3.6-4-82-3.js
 * @description Object.defineProperty - Update [[Configurable]] attribute of 'name' property to false successfully when [[Configurable]] attribute of 'name' property is true,  the 'desc' is a generic descriptor which contains [[Configurable]] attribute as false, 'name' property is a data property (8.12.9 step 8)
 */


function testcase() {
    
        var obj = {};

        Object.defineProperty(obj, "foo", {
            value: 1001,
            writable: true,
            enumerable: true,
            configurable: true
        });

        Object.defineProperty(obj, "foo", {
            configurable: false
        });

        return dataPropertyAttributesAreCorrect(obj, "foo", 1001, true, true, false);
    }
runTestCase(testcase);