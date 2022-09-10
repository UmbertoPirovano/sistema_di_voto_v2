package gui;

import java.net.URL;
import java.util.Objects;
import java.util.ResourceBundle;

import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.fxml.Initializable;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.ChoiceBox;
import javafx.scene.control.PasswordField;
import javafx.scene.control.TextField;
import javafx.stage.Stage;
import system.SystemEvote;
import users.Elector;
import users.User;

public class AdminElectorEditorController implements Initializable {

    @FXML
    private Button confirmButton;

    @FXML
    private TextField fieldBirthDay;

    @FXML
    private TextField fieldCf;

    @FXML
    private ChoiceBox<String> fieldGender;

    @FXML
    private TextField fieldName;

    @FXML
    private PasswordField fieldPassword;

    @FXML
    private TextField fieldSurname;

    @FXML
    void confirm(ActionEvent event) {
    	try {
    		String cf = fieldCf.getText();
    		String password = fieldPassword.getText();
    		String name = fieldName.getText();
    		String surname = fieldSurname.getText();
    		String gender = fieldGender.getValue();
    		String birthDay = fieldBirthDay.getText();
    		if(!checkFiscalCode(name,surname,birthDay,gender,cf)) {
    			showErrorMessage((new IllegalArgumentException("Formato del codice fiscale errato")).getMessage());
    			return;
    		}
    		User u = new Elector(cf,password,name,surname);
    		SystemEvote.getInstance().addUser(u, password);
    	} catch(Exception e) {
    		showErrorMessage(e.getMessage());
    	}
    }

	@Override
	public void initialize(URL location, ResourceBundle resources) {
		fieldGender.getItems().addAll("M", "F");
		fieldGender.setValue("M");
	}

	/**
	 * Verifica che il codice fiscale passato come parametro corrisponda a quello ricavato dagli altri parametri.
	 * @param name
	 * @param surname
	 * @param birthDay
	 * @param birthPlace
	 * @param gender
	 * @param homeCity
	 * @param cf
	 * @return True se cf è uguale a quello ricavato dagli altri parametri, false altrimenti.
	 */
	private static boolean checkFiscalCode(String name,String surname,String birthDay,  String gender, String cf) {
		int day = 0;
		int month = 0;
		int year = 0;
		int i = 0;
		int j = 0;
		String acc = "";

		while(j<birthDay.length()) {
			if(birthDay.charAt(j) == '/') {
				switch(i) {
				case 0:
					day = Integer.parseInt(acc);
					break;
				case 1:
					month = Integer.parseInt(acc);
					break;
				default:
					throw new IllegalArgumentException("Formato della data di nascita errato");
				}
				acc = new String("");
				i++;
			} else {
				acc += birthDay.charAt(j);
			}
			if(j==birthDay.length()-1){
				year = Integer.parseInt(acc);
			}
			j++;
		}

		String codiceVerifica = generateTaxCode(name, surname, day, month, year, gender.charAt(0));

		return codiceVerifica.equals(cf.substring(0, 11));
	}

	public static String removeVowels(String s){
		String s_cons = s.replace("A", "");
		s_cons = s_cons.replace("E", "");
		s_cons = s_cons.replace("I", "");
		s_cons = s_cons.replace("O", "");
		s_cons = s_cons.replace("U", "");
		return s_cons;
	}

    public static String removeConsonants(String s){
		String s_vo = "";
		for(int i = 0 ; i < s.length() ; i++){
			if(isVowel(s.charAt(i))) s_vo += s.charAt(i);
		}
		return s_vo;
	}

    public static boolean isVowel(char c){
		if(c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U')
			return true;
		return false;
	}

    public static String generateTaxCode(String name, String surname, int gg, int mm, int aa, char sesso){
		surname = surname.toUpperCase(); //Conterrà il cognome formattato per il codice fiscale
		name = name.toUpperCase(); //Conterrà il nome formattato per il codice fiscale

		//primi tre caratteri
		String surname_cons = removeVowels(surname);
		String surname_vo = removeConsonants(surname);
		if(surname_cons.length() > 3)
			surname_cons= surname_cons.substring(0, 3);
		int j = 0;
		while(surname_cons.length() < 3){
			if(j < surname_vo.length())
				surname_cons += surname_vo.charAt(j++);
			else
				surname_cons += "X";
		}

		//successivi 3 caratteri
		String name_cons = removeVowels(name);
		String name_vo = removeConsonants(name);
		if(name_cons.length() > 3)
			name_cons = name_cons.charAt(0) + "" + name_cons.charAt(2) + "" + name_cons.charAt(3);
		j = 0;
		while(name_cons.length() < 3){
			if(j < name_vo.length())
				name_cons += name_vo.charAt(j++) ;
			else
				name_cons += "X";
		}

		//2 caratteri per lánno
		String year = String.valueOf(aa).substring(2); //Conterrà l'anno formattato per il codice fiscale

		//lettera per il mese
		char month = ' ';
		switch(mm){
			case 1:
				month = 'A';
				break;
			case 2:
				month = 'B';
				break;
			case 3:
				month = 'C';
				break;
			case 4:
				month = 'D';
				break;
			case 5:
				month = 'E';
				break;
			case 6:
				month = 'H';
				break;
			case 7:
				month = 'L';
				break;
			case 8:
				month = 'M';
				break;
			case 9:
				month = 'P';
				break;
			case 10:
				month = 'R';
				break;
			case 11:
				month = 'S';
				break;
			case 12:
				month = 'T';
		}

		//due caratteri per il giorno di nascita
		String day = "";
		if(sesso == 'M'){
			if(gg < 10) day += "0" + gg;
		    else day += gg;
		}
		if(sesso == 'F'){
			day += (gg + 40);
		}


		return surname_cons + "" + name_cons + "" + year + "" + month + "" + day;
	}

	private void showErrorMessage(String s) {
		Objects.requireNonNull(s);
		String msg = "ERROR:\n\n";
		msg += s;
		try {
			FXMLLoader loader = new FXMLLoader(getClass().getResource("GeneralMessage.fxml"));
    		GeneralMessageController controller = new GeneralMessageController(msg);
    		loader.setController(controller);
    		Parent root = loader.load();
            Stage stage = new Stage();
        	stage.setTitle("ERROR");
        	stage.setScene(new Scene(root, 600, 400));
        	stage.setResizable(false);
        	stage.show();
		} catch (Exception e) {
			showErrorMessage(e.getMessage());
			e.printStackTrace();
		}
	}

}
