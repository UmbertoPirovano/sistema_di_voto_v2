package gui;

import java.util.Objects;

import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.PasswordField;
import javafx.scene.control.TextField;
import javafx.stage.Stage;
import system.SystemEvote;
import users.Administrator;
import users.User;

public class AdminAdministratorEditorController {

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
    		String username = fieldUsername.getText();
    		String password = fieldPassword.getText();
    		String name = fieldName.getText();
    		String surname = fieldSurname.getText();
    		User u = new Administrator(username, password);
    		SystemEvote.getInstance().addUser(u, password);
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

}
