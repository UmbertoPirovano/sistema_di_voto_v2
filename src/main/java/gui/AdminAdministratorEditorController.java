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
import javafx.scene.control.PasswordField;
import javafx.scene.control.TextField;
import javafx.stage.Stage;
import system.SystemEvote;
import users.Administrator;
import users.User;

public class AdminAdministratorEditorController implements Initializable {

    @FXML
    private Button confirmButton;

    @FXML
    private TextField fieldName;

    @FXML
    private PasswordField fieldPassword;

    @FXML
    private TextField fieldSurname;

    @FXML
    private TextField fieldUsername;

    @FXML
    void confirm(ActionEvent event) {
    	try {
    		
    		String username = Objects.requireNonNull(fieldUsername.getText());
    		String password = Objects.requireNonNull(fieldPassword.getText());
    		String name = Objects.requireNonNull(fieldName.getText());
    		String surname = Objects.requireNonNull(fieldSurname.getText());
    		User u = new Administrator(username, password);
    		SystemEvote.getInstance().addUser(u, password);
    	} catch(NullPointerException npe) {
    		showErrorMessage("Non sono stati settati tutti i campi");
    	} catch(Exception e) {
    		showErrorMessage(e.getMessage());
    	}
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

	@Override
	public void initialize(URL location, ResourceBundle resources) {
		confirmButton.setText(null);
		fieldName.setText(null);
		fieldPassword.setText(null);
		fieldSurname.setText(null);
		fieldUsername.setText(null);
	}

}
