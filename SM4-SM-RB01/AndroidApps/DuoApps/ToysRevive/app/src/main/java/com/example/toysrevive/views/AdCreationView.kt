package com.example.toysrevive.views

import android.net.Uri

import androidx.compose.foundation.layout.*
import androidx.compose.foundation.lazy.LazyColumn
import androidx.compose.foundation.shape.RoundedCornerShape
import androidx.compose.foundation.text.KeyboardActions

import androidx.compose.material.*
import androidx.compose.runtime.*

import kotlinx.coroutines.launch

import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.unit.dp
import com.example.toysrevive.models.*

import com.example.toysrevive.utils.GlobalSettings
import com.example.toysrevive.widgets.GalleryGrid

@OptIn(ExperimentalMaterialApi::class)
@Composable
fun AdCreationView(scaffoldState: ScaffoldState, modifier: Modifier = Modifier) {
    var toyName by remember { mutableStateOf("") }
    var toyDescription by remember { mutableStateOf("") }

    var toyKindExpanded by remember { mutableStateOf(false) }
    var toyStateExpanded by remember { mutableStateOf(false) }

    var toyKindSelected by remember { mutableStateOf(0) }
    var toyStateSelected by remember { mutableStateOf(0) }

    val images = mutableListOf<Uri?>(null, null, null, null, null, null)

    val scope = rememberCoroutineScope()

    LazyColumn(
        verticalArrangement = Arrangement.Center,
        horizontalAlignment = Alignment.CenterHorizontally,
        modifier = modifier
    ) {
        item {
            GalleryGrid(
                images,
                modifier = Modifier.padding(8.dp)
            )
            TextField(
                value = toyName,
                onValueChange = {
                    toyName = it
                },
                label = { Text(text = "Toy name") },
                placeholder = { Text(text = "The name of the toy you want to give") },
                keyboardActions = KeyboardActions.Default,
                maxLines = 1,
                colors = TextFieldDefaults.textFieldColors(
                    textColor = MaterialTheme.colors.onSurface,
                    backgroundColor = MaterialTheme.colors.surface
                ),
                shape = RoundedCornerShape(5.dp),
                modifier = Modifier
                    .fillMaxWidth()
                    .padding(5.dp)
            )
            ExposedDropdownMenuBox(
                expanded = toyKindExpanded,
                onExpandedChange = { toyKindExpanded = !toyKindExpanded }
            ) {
                TextField(
                    value = toyKindCorres[toyKindSelected],
                    onValueChange = {},
                    readOnly = true,
                    trailingIcon = {
                        ExposedDropdownMenuDefaults.TrailingIcon(
                            expanded = toyKindExpanded
                        )
                    },
                    colors = ExposedDropdownMenuDefaults.textFieldColors(
                        textColor = MaterialTheme.colors.onSurface,
                        backgroundColor = MaterialTheme.colors.surface
                    ),
                    shape = RoundedCornerShape(5.dp),
                    modifier = Modifier
                        .fillMaxWidth()
                        .padding(5.dp)
                )
                ExposedDropdownMenu(
                    expanded = toyKindExpanded,
                    onDismissRequest = { toyKindExpanded = false }
                ) {
                    enumValues<ToyKind>().forEachIndexed { index, _ ->
                        DropdownMenuItem(
                            onClick = {
                                toyKindSelected = index
                                toyKindExpanded = false
                            }
                        ) {
                            Text(text = toyKindCorres[index])
                        }
                    }
                }
            }
            ExposedDropdownMenuBox(
                expanded = toyStateExpanded,
                onExpandedChange = { toyStateExpanded = !toyStateExpanded }
            ) {
                TextField(
                    value = obsolescenceCorres[toyStateSelected],
                    onValueChange = {},
                    readOnly = true,
                    trailingIcon = {
                        ExposedDropdownMenuDefaults.TrailingIcon(
                            expanded = toyStateExpanded
                        )
                    },
                    colors = ExposedDropdownMenuDefaults.textFieldColors(
                        textColor = MaterialTheme.colors.onSurface,
                        backgroundColor = MaterialTheme.colors.surface
                    ),
                    shape = RoundedCornerShape(5.dp),
                    modifier = Modifier
                        .fillMaxWidth()
                        .padding(5.dp)
                )
                ExposedDropdownMenu(
                    expanded = toyStateExpanded,
                    onDismissRequest = { toyStateExpanded = false }
                ) {
                    enumValues<ObsolescenceState>().forEachIndexed { index, _ ->
                        DropdownMenuItem(
                            onClick = {
                                toyStateSelected = index
                                toyStateExpanded = false
                            }
                        ) {
                            Text(text = obsolescenceCorres[index])
                        }
                    }
                }
            }
            TextField(
                value = toyDescription,
                onValueChange = {
                    toyDescription = it
                },
                label = { Text(text = "Toy description") },
                placeholder = { Text(text = "The description of the toy you want to give") },
                singleLine = false,
                maxLines = 6,
                colors = TextFieldDefaults.textFieldColors(
                    textColor = MaterialTheme.colors.onSurface,
                    backgroundColor = MaterialTheme.colors.surface
                ),
                shape = RoundedCornerShape(5.dp),
                modifier = Modifier
                    .fillMaxWidth()
                    .padding(5.dp)
            )
            Button(
                enabled = (toyName != "" && toyKindSelected != 0 && toyStateSelected != 0 && toyDescription != ""),
                onClick = {
                    GlobalSettings.createNewToy(
                        toyName,
                        toyDescription,
                        images.filterNotNull(),
                        enumValues<ObsolescenceState>()[toyStateSelected],
                        enumValues<ToyKind>()[toyKindSelected]
                    )
                    scope.launch {
                        when (scaffoldState.snackbarHostState.showSnackbar("Toy has been added to our catalog. Thank you for your donation! ❤")) {
                            else -> {}
                        }
                    }
                    toyName = ""
                    toyDescription = ""
                    toyKindSelected = 0
                    toyStateSelected = 0
                }
            ) {
                Text("Submit toy ad")
            }
        }
    }
}
