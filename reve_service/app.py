from flask import Flask
from flask import request
import os
import shutil 

app = Flask(__name__)

@app.route('/reve/',methods=['POST'])
def run_llreve_script():
    	execution_id = request.form['id']
	fun = request.form['fun_name']
	side0 = request.form['side0']
	side1 = request.form['side1']
	#assumed_equivalent = request.form['assumed_equivalent']
	if not os.path.exists(execution_id): 
		os.makedirs(execution_id)
	file1 = write_file_content(0,side0,execution_id)
	file2 = write_file_content(1,side1,execution_id)
	command = 'llreve.py -z3 {} {} -infer-marks -fun {}'.format(file1,file2,fun)
	print('EXECUTING {}'.format(command))
	result = os.popen(command).read()
	shutil.rmtree(execution_id)
	return result
	

@app.route('/revecheck/')
def test_service():
        return 'LLREVE service is up'

def write_file_content(num,content,folder_name):
	#print('write file{}'.format(num))
	file_name = '{}/p{}.c'.format(folder_name,num)
	with open(file_name,'w') as program_file:
        	program_file.write(content)
	#print('file{} written'.format(num))
	return file_name





if __name__ == '__main__':
      app.run(host='0.0.0.0',port=3017)
