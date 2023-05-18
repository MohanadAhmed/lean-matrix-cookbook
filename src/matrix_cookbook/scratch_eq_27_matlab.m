A = sym('A_', [4 4]);
trace(A*A*A);
x = det(eye(4) + A) - det(A) - 1;
y = trace(A) + (1/2)*trace(A)^2 - (1/2)*trace(A*A) ...
+ (1/6)*trace(A)^3 - (1/2)*trace(A)*trace(A*A) + (1/3)*trace(A*A*A);
simplify(x - y)
str_x = char(x);
str_x = replace(str_x, '1', '0');
str_x = replace(str_x, '2', '1');
str_x = replace(str_x, '3', '2');
str_x = replace(str_x, '4', '3');

z = expand(trace(A)*trace(A));
str_x = char(z);
str_x = replace(str_x, '1', '0');
str_x = replace(str_x, '2', '1');
str_x = replace(str_x, '3', '2');
str_x = replace(str_x, '4', '3');

%% 
q = expand(trace(A)^2) - trace(A*A);
str_x = char(q);
str_x = replace(str_x, '_1', '_0');
str_x = replace(str_x, '_2', '_1');
str_x = replace(str_x, '_3', '_2');
str_x = replace(str_x, '_4', '_3');
str_x = replace(str_x, '_', ' ');

%%
q = expand(trace(A)^3) - expand(3 * trace(A)*expand(trace(A*A))) + expand(2*trace(A*A*A));
str_x = char(q);
str_x = replace(str_x, '_1', '_0');
str_x = replace(str_x, '_2', '_1');
str_x = replace(str_x, '_3', '_2');
str_x = replace(str_x, '_4', '_3');
str_x = replace(str_x, '_', ' ');
str_x
