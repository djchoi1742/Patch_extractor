from tkinter import *
from tkinter.filedialog import *
import os
import numpy as np
import pandas as pd
import pydicom as dcm
import pydicom.uid
from pydicom.dataset import Dataset, FileDataset
import re
import glob
import datetime
import time
import math
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from matplotlib.figure import Figure
import matplotlib.pyplot as plt


def str_extract(string, text):
    extract = re.search(string, text)
    if extract is None:
        matching = None
    else:
        matching = extract.group()
    return matching

menu_font = ('Helvetica', 15)
base_font = ('Helvetica', 12)


class ViewerMRI:
    def __init__(self):
        self.gui = Tk()
        self.gui.title('Texture extractor for MRI Image')
        self.gui.call('tk', 'scaling', 1.2)
        ws, hs = self.gui.winfo_screenwidth(), self.gui.winfo_screenheight()
        w, h = 800, 720
        x, y = (ws / 6) - (w / 6), (hs / 2) / (h / 2)
        self.gui.geometry('%dx%d+%d+%d' % (w, h, x, y))

        self.set_wd = None  # base directory
        self.save_wd = None
        self.folder_path = None
        self.select_dcm = None
        self.canvas = None
        self.grid_color = 'dodgerblue'  # default horizontal & vertical line color
        self.patch_color = 'darkorange'  # default patch border color

        self.study_num, self.slice_num = None, None  # study & slice index
        self.is_grid = False  # whether there is a grid in the image

        self.div_num = 8 # default grid interval
        self.image_dpi = 32  # default dpi
        self.f_size = 16  # figure size, set self.image_dpi * self.f_size = 512 (MRI image row & column)

        #self.patch_num = 0  # the number of patches checked in the image
        self.patch_array = {}  # save patch images
        self.select_patches = {}  # display checked grid area
        self.is_patch = {}

        self.patch_num = 0

        self.study_index = IntVar()
        self.study_index.set(-1)
        self.sop_index = IntVar()
        self.sop_index.set(-1)

        self.menu_bar = Menu(self.gui)
        file_menu = Menu(self.menu_bar, tearoff=0)
        file_menu.add_command(label='Select Folder...', font=menu_font, command=self.select_folder)
        self.menu_bar.add_cascade(label='File', font=menu_font, menu=file_menu)

        export_menu = Menu(self.menu_bar, tearoff=0)
        export_menu.add_command(label='Select Save Folder...', font=menu_font, command=self.save_folder)
        export_menu.add_command(label='Export Result...', font=menu_font, command=self.export_result)
        self.menu_bar.add_cascade(label='Export', font=menu_font, menu=export_menu)

        help_menu = Menu(self.menu_bar, tearoff=0)
        help_menu.add_command(label='Help...', font=menu_font)
        self.menu_bar.add_cascade(label='Help', font=menu_font, menu=help_menu)

        self.gui.config(menu=self.menu_bar)

        self.frame10 = Frame(self.gui)

        self.study_desc = Label(self.frame10, width=45, text='Study Description',
                                background='midnightblue', foreground='snow', font=base_font)
        self.study_desc.grid(row=0, column=0)

        self.slice_desc = Label(self.frame10, width=45, text='Image Description',
                                background='indianred', foreground='snow', font=base_font)
        self.slice_desc.grid(row=0, column=1)

        self.study_check = Label(self.frame10, width=45, text='Study Check',
                                  background='royalblue', foreground='snow', font=base_font)
        self.study_check.grid(row=1, column=0)

        self.slice_check = Label(self.frame10, width=45, text='Series Check',
                                  background='deeppink', foreground='snow', font=base_font)
        self.slice_check.grid(row=1, column=1)

        self.coord_window = Label(self.frame10, width = 45, text="Coordinates: ",
                                   background='lightskyblue', foreground='black', font=base_font)
        self.coord_window.grid(row=2, column=0)
        self.grid_select = Label(self.frame10, width = 45, text="Grid select",
                                 background='pink', foreground='black', font=base_font)
        self.grid_select.grid(row=2, column=1)

        self.save_path = Label(self.frame10, width=45, text='Save path',
                               background='aqua', foreground='black', font=base_font)
        self.save_path.grid(row=3, column=0)

        self.cond_window = Label(self.frame10, width=45, text='Condition window',
                                 background='mistyrose', foreground='black', font=base_font)
        self.cond_window.grid(row=3, column=1)
        self.frame10.pack()

        self.frame11 = Frame(self.gui)
        self.grid_adjust_button = Button(self.frame11, width=25, text='Grid Adjust', font=base_font,
                                  background='navy', foreground='snow', command=self.adjust_grid)
        self.grid_adjust_button.grid(row=0, column=0)

        self.grid_button = Button(self.frame11, width = 25, text='Add Grid', font=base_font,
                                  background='firebrick', foreground='snow', command=self.add_grid)
        self.grid_button.grid(row=0, column=1)

        self.frame11.pack()

        self.frame12 = Frame(self.gui)
        self.f12_study_prev = Button(self.frame12, text='Study Prev', font=base_font, command=self.study_prev)
        self.f12_study_prev.grid(row=1, column=0)
        self.f12_study_next = Button(self.frame12, text='Study Next', font=base_font, command=self.study_next)
        self.f12_study_next.grid(row=1, column=2)
        self.f12_prev = Button(self.frame12, text="Image Prev", font=base_font, command=self.slice_prev)
        self.f12_prev.grid(row=0, column=1)
        self.f12_next = Button(self.frame12, text="Image Next", font=base_font, command=self.slice_next)
        self.f12_next.grid(row=1, column=1)
        self.frame12.pack()

        self.frame13 = Frame(self.gui, width=100, height=100)
        self.canvas = None
        self.frame13.pack(side=TOP)

        self.gui.bind("<a>", self.adjust_grid_key)

    def select_folder(self):
        self.set_wd = askdirectory(title='Select Folder', mustexist=1)

        if self.set_wd is None:
            return
        if self.set_wd:
            self.folder_totallist = sorted(os.listdir(self.set_wd))

            self.folder_list = []
            for path in self.folder_totallist:
                if os.path.isdir(os.path.join(self.set_wd, path)):
                    self.folder_list.append(path)

            self.study_index.set(1)
            self.sop_index.set(1)

            self.study_num = len(self.folder_list)

            self.go_to_image(self.study_index, self.sop_index)
            self.image_setting(self.study_index, self.sop_index)

    def save_folder(self):
        self.save_wd = askdirectory(title='Select Save Folder', mustexist=1)
        if self.save_wd is None:
            return
        if self.save_wd:
            self.save_path.config(text='Save dir: '+self.save_wd)

    def export_result(self):
        if self.save_wd is not None:
            count = 0
            for pw in range(0, self.div_num + 1):
                for ph in range(0, self.div_num + 1):
                    if self.is_patch[str(pw) + '_' + str(ph)]:
                        save_name = self.folder_name+'_'+re.sub('.dcm', '', self.dcm_name)+\
                                    '_%03d_%03d_%03d'%(self.div_num, pw+1, ph+1)+'.dcm'
                        save_file = os.path.join(self.save_wd, save_name)
                        self.write_dcm(self.patch_array[str(pw) + '_' + str(ph)], pw+1, ph+1, save_file)
                        count += 1

            self.cond_window.config(text='%d ' % count + self.cond_sentence(count) + ' saved')
        else:
            self.error_box('Error! Please set a save path first.')

    def adjust_grid_value(self):
        if self.canvas is not None:
            if self.is_grid:
                for iw in range(0, int(math.ceil(self.div_num))):
                    self.v_lines[iw].remove()
                for ih in range(0, int(math.ceil(self.div_num))):
                    self.h_lines[ih].remove()

                for pw in range(0, self.div_num+1):
                    for ph in range(0, self.div_num+1):
                        if self.is_patch[str(pw) + '_' + str(ph)]:
                            self.patch_remove(str(pw) + '_' + str(ph))

                self.canvas.draw()
                self.is_grid = False
                self.patch_array = {}
                self.grid_button.config(text='Add Grid')

        self.div_num = self.adjust_value.get()

        self.grid_adjust_button.config(text='Grid Interval: %d' % self.div_num)

        self.patch_num = 0
        self.cond_window.config(text='%d ' % self.patch_num +
                                     self.cond_sentence(self.patch_num) + ' selected')

        self.adjust_popup.destroy()

    def adjust_grid_value_key(self, event):
        self.adjust_grid_value()

    def adjust_grid(self):
        self.adjust_popup = Toplevel()
        self.adjust_popup.geometry('200x80')

        adjust_label = Label(self.adjust_popup, text='Grid Interval Settings', font=base_font)
        adjust_label.pack()
        self.adjust_value = IntVar()
        self.adjust_value.set(self.div_num)
        self.entry_value = Entry(self.adjust_popup, textvariable=self.adjust_value, font=base_font)
        self.entry_value.pack()

        self.enter_button = Button(self.adjust_popup, text='Enter', command=self.adjust_grid_value)
        self.enter_button.pack()

        self.adjust_popup.bind('<Return>', self.adjust_grid_value_key)
        self.adjust_popup.mainloop()

    def adjust_grid_key(self, event):
        self.adjust_grid()

    def go_to_image(self, study_index, sop_index):
        try:
            self.folder_name = self.folder_list[study_index.get() - 1]
            self.dcm_list = sorted(glob.glob(os.path.join(self.set_wd, self.folder_name)+'/*.dcm'))
            self.slice_num = len(self.dcm_list)

            if sop_index.get() > self.slice_num:
                sop_index.set(self.slice_num)

            self.current_dcm = self.dcm_list[sop_index.get() - 1]
            self.dcm_name = os.path.basename(self.current_dcm)

            self.ds = dcm.read_file(self.current_dcm)
            self.image_array = self.ds.pixel_array
        except:
            self.error_box('Error! Please check for dicom files in subfolders.')

    def image_setting(self, study_index, sop_index):
        if self.canvas is None:
            self.f1 = Figure(figsize=(self.f_size, self.f_size), dpi=self.image_dpi)
            self.ax = self.f1.add_axes((0, 0, 1, 1), frameon=True)
            self.ax.xaxis.set_visible(False)
            self.ax.yaxis.set_visible(False)

            self.ax.imshow(self.image_array, cmap='gray')

            self.canvas = FigureCanvasTkAgg(self.f1, master=self.frame13)
            self.canvas.get_tk_widget().pack()
            #self.canvas.get_tk_widget().pack(side=TOP, fill=BOTH, expand=1)
            self.canvas.draw()

            self.gui.bind('<space>', self.slice_next_key)
            self.gui.bind('<Left>', self.study_prev_key)
            self.gui.bind('<Right>', self.study_next_key)
            self.gui.bind("<Up>", self.slice_prev_key)
            self.gui.bind("<Down>", self.slice_next_key)
            self.gui.bind("<g>", self.add_grid_key)

            self.canvas.callbacks.connect('motion_notify_event', self.motion_coord)
            self.canvas.callbacks.connect('button_press_event', self.press_mouse)
        else:
            self.ax.clear()
            self.ax.imshow(self.image_array, cmap='gray')
            self.canvas.draw()

        #self.save_idx = 1
        self.is_grid = False
        self.patch_num = 0
        self.study_desc.config(text='Study index:  '+str(study_index.get()) + '/' + str(self.study_num))
        self.slice_desc.config(text='Slice Index:  '+str(sop_index.get()) + '/' + str(self.slice_num))
        self.slice_check.config(text='Width: %d, Height: %d' % (self.ds.Columns, self.ds.Rows))
        self.study_check.config(text='Study name: '+self.folder_name)
        self.cond_window.config(text='%d patches selected' % self.patch_num)

    def motion_coord(self, event):
        if event.inaxes is not None:
            self.coord_window.config(text="X: " + str(int(event.xdata)) + "   " +
                                          "Y: " + str(int(event.ydata)), font=("Helvetica", 12))
        else:
            return

    def move_button(self, function, num_type, total_type):
        if self.set_wd is None:
            self.error_box('Error! Please upload folder.')
            return
        else:
            num_type.set(function(num_type.get(), total_type))
            self.go_to_image(self.study_index, self.sop_index)
            self.image_setting(self.study_index, self.sop_index)

    def index_minus(self, num, index_total):
        if num <= 0 or num > index_total:
            num = None
        max_num = index_total
        if num != 1:
            num -= 1
        else:
            num = max_num
        return num

    def index_plus(self, num, index_total):
        if num <= 0 or num > index_total:
            num = None
        max_num = index_total
        if num < max_num and num is not None:
            num += 1
        elif num == max_num:
            num = 1
        return num

    def slice_next(self):
        self.move_button(self.index_plus, self.sop_index, self.slice_num)

    def slice_prev(self):
        self.move_button(self.index_minus, self.sop_index, self.slice_num)

    def slice_next_key(self, event):
        self.move_button(self.index_plus, self.sop_index, self.slice_num)

    def slice_prev_key(self, event):
        self.move_button(self.index_minus, self.sop_index, self.slice_num)

    def study_next(self):
        self.move_button(self.index_plus, self.study_index, self.study_num)

    def study_prev(self):
        self.move_button(self.index_minus, self.study_index, self.study_num)

    def study_next_key(self, event):
        self.move_button(self.index_plus, self.study_index, self.study_num)

    def study_prev_key(self, event):
        self.move_button(self.index_minus, self.study_index, self.study_num)

    def add_grid(self):
        if self.div_num >= 1:  # whether valid div_num
            if self.is_grid is False:
                if self.canvas is None:
                    self.error_box('Error! Please upload image.')
                else:
                    #self.w_interval = int(self.ds.Columns / self.div_num)
                    #self.h_interval = int(self.ds.Rows / self.div_num)

                    self.w_interval = self.ds.Columns / self.div_num
                    self.h_interval = self.ds.Rows / self.div_num

                    self.v_lines, self.h_lines = {}, {}
                    print('div_num: ', self.div_num)
                    for iw in range(0, self.div_num):
                        self.v_lines[iw] = self.ax.axvline(round(iw*self.w_interval), color=self.grid_color)
                    for ih in range(0, self.div_num):
                        self.h_lines[ih] = self.ax.axhline(round(ih*self.h_interval), color=self.grid_color)
                    self.is_grid = True

                    for pw in range(0, self.div_num+1):
                        for ph in range(0, self.div_num+1):
                            self.is_patch[str(pw)+'_'+str(ph)] = False

                    self.canvas.draw()
                    self.grid_button.config(text='Remove Grid')
            else:
                for iw in range(0, self.div_num):
                    self.v_lines[iw].remove()
                for ih in range(0, self.div_num):
                    self.h_lines[ih].remove()

                for pw in range(0, self.div_num + 1):
                    for ph in range(0, self.div_num + 1):
                        if self.is_patch[str(pw)+'_'+str(ph)]:
                            self.patch_remove(str(pw) + '_' + str(ph))

                self.patch_num = 0
                self.cond_window.config(text='%d ' % self.patch_num + self.cond_sentence(self.patch_num) + ' selected')

                self.canvas.draw()
                self.is_grid = False
                self.grid_button.config(text='Add Grid')
        else:
            self.error_box('Error! Invalid grid interval. Please set grid interval to 1 or higher.')

    def add_grid_key(self, event):
        self.add_grid()

    def press_mouse(self, event):
        def fine_adjustment(value, threshold, direction):
            if value >= threshold:
                if direction == 0:
                    pass
                else:
                    value = threshold - 2
            return value

        if self.is_grid:
            press_x, press_y = int(event.xdata // self.w_interval), int(event.ydata // self.h_interval)
            self.grid_select.config(text='Area X range: %d, Y range: %d' % (press_x+1, press_y+1))

            patch_idx = str(press_x) + '_' + str(press_y)

            if self.is_patch[patch_idx] is False:
                y_top, y_bottom = round(press_y * self.h_interval), round((press_y + 1) * self.h_interval)
                x_left, x_right = round(press_x * self.w_interval), round((press_x + 1) * self.w_interval)

                self.patch_image = self.image_array[y_top:y_bottom, x_left:x_right]

                x_right_value = fine_adjustment(x_right,   self.ds.Columns, 1)
                y_bottom_value = fine_adjustment(y_bottom,  self.ds.Rows, 1)

                self.select_patches[patch_idx] = {}
                self.select_patches[patch_idx]['left'] = self.ax.axvline(x=x_left,
                                                              ymin= 1 - (y_top/self.ds.Rows),
                                                              ymax= 1 - (y_bottom_value/self.ds.Rows),
                                                              color=self.patch_color, linewidth=2.5)


                self.select_patches[patch_idx]['right'] = self.ax.axvline(x=x_right_value,
                                                               ymin= 1 - (y_top / self.ds.Rows),
                                                               ymax= 1 - (y_bottom_value / self.ds.Rows),
                                                               color=self.patch_color, linewidth=2.5)

                self.select_patches[patch_idx]['top'] = self.ax.axhline(y=y_top,
                                                             xmin=x_left / self.ds.Columns,
                                                             xmax=x_right_value / self.ds.Columns,
                                                             color=self.patch_color, linewidth=2.5)

                self.select_patches[patch_idx]['bottom'] = self.ax.axhline(y=y_bottom_value,
                                                                xmin=x_left / self.ds.Columns,
                                                                xmax=x_right_value / self.ds.Columns,
                                                                color=self.patch_color, linewidth=2.5)

                self.canvas.draw()
                self.is_patch[patch_idx] = True
                self.patch_array[patch_idx] = self.patch_image
                self.patch_num += 1

                self.cond_window.config(text='%d '%self.patch_num+self.cond_sentence(self.patch_num)+' selected')

            else:
                self.patch_remove(patch_idx)
                self.canvas.draw()
                self.patch_num -= 1
                self.is_patch[patch_idx] = False
                self.patch_array[patch_idx] = None

                self.cond_window.config(text='%d ' % self.patch_num + self.cond_sentence(self.patch_num)+' selected')

            if False:
                self.patch_popup = Toplevel()
                self.patch_popup.title('Patch image view')

                pws, phs = self.patch_popup.winfo_screenwidth(), self.patch_popup.winfo_screenheight()
                pw, ph = 200, 160
                px, py = 3.6*((pws / 6) - (pw / 6)), 10*((phs / 2) / (ph / 2))
                self.patch_popup.geometry('%dx%d+%d+%d' % (pw, ph, px, py))
                self.frame20 = Frame(self.patch_popup, width=50, height=50)

                self.f2 = Figure(figsize=(int(self.f_size/self.div_num), int(self.f_size/self.div_num)),
                                 dpi=self.image_dpi)

                self.patch_board = self.f2.add_axes((0,0,1,1), frameon=True)
                self.patch_board.xaxis.set_visible(False)
                self.patch_board.yaxis.set_visible(False)
                self.patch_board.imshow(self.patch_image, cmap='gray')

                self.patch_canvas = FigureCanvasTkAgg(self.f2, master=self.frame20)
                self.patch_canvas.get_tk_widget().pack()

                self.patch_canvas.draw()

                self.save_button = Button(self.frame20, text='Save', width=12,
                                          font=base_font, command=self.patch_save)
                self.save_button.pack()
                self.frame20.pack()

                self.patch_popup.bind('s', self.patch_save_key)
        else:
            self.error_box('Error! Please click to add the grid first.')

    def patch_remove(self, patch_idx):
        self.select_patches[patch_idx]['left'].remove()
        self.select_patches[patch_idx]['right'].remove()
        self.select_patches[patch_idx]['top'].remove()
        self.select_patches[patch_idx]['bottom'].remove()
        self.is_patch[patch_idx] = False

    def _patch_save(self):
        try:
            self.initial_name = re.sub('.dcm', '', self.dcm_name)+'_%03d' % self.save_idx
            save_file = asksaveasfilename(title='Save patch image',
                                          initialfile=self.folder_name+'_'+self.initial_name+'.dcm',
                                          filetypes=(('DICOM files', '*.dcm'), ('All files', '*.*')))
            if save_file is None:
                return
            if save_file:
                #self.f2.savefig(save_file)
                self.write_dcm(self.patch_image, save_file)
                self.save_idx += 1
                self.patch_popup.destroy()
        except:
            self.error_box('Error! Please click the mouse in the image.')

    def _patch_save_key(self, event):
        self.patch_save()

    def cond_sentence(self, patch_num):
        if patch_num == 1:
            num_count = 'patch'
        else:
            num_count = 'patches'
        return num_count

    def write_dcm(self, pixel_array, pw, ph, filename):
        read_meta = dcm.filereader.read_file_meta_info(self.current_dcm)

        file_meta = Dataset()
        file_meta.MediaStorageSOPClassUID = 'MR patch image storage'
        file_meta.MediaStorageSOPInstanceUID = read_meta.MediaStorageSOPInstanceUID
        file_meta.ImplementationClassUID = read_meta.ImplementationClassUID

        ds = FileDataset(filename, {}, file_meta=file_meta, preamble=b'\x00'*128)

        ds.file_meta.TransferSyntaxUID = dcm.uid.ImplicitVRLittleEndian
        ds.Modality = 'MR'
        ds.ContentDate = str(datetime.date.today()).replace('-', '')
        ds.ContentTime = str(time.time())

        ds.StudyInstanceUID = self.ds.StudyInstanceUID
        ds.SeriesInstanceUID = self.ds.SeriesInstanceUID+'001'
        ds.SOPClassUID = self.ds.SOPClassUID + '%03d' % pw + '%03d' % ph
        ds.SOPInstanceUID = self.ds.SOPInstanceUID + '%03d' % pw+'%03d' % ph
        ds.SecondaryCaptureDeviceManufactur = 'Python 3.6.0'

        ds.StudyID = self.ds.StudyID
        ds.SeriesNumber = self.ds.SeriesNumber
        ds.AcquisitionNumber = self.ds.AcquisitionNumber
        ds.InstanceNumber = self.ds.InstanceNumber
        ds.StudyDescription = 'MR patch study'
        ds.SeriesDescription = 'MR patch series'

        ds.PatientName = self.ds.PatientName
        ds.PatientID = self.ds.PatientID
        ds.PatientSex = self.ds.PatientSex
        ds.PatientAge = self.ds.PatientAge
        ds.PatientWeight = self.ds.PatientWeight

        ds.SamplesPerPixel = 1
        ds.PhotometricInterpretation = 'MONOCHROME2'
        ds.PixelRepresentation = 0
        ds.HighBit = self.ds.HighBit
        ds.BitsStored = self.ds.BitsStored
        ds.BitsAllocated = self.ds.BitsAllocated
        ds.SmallestImagePixelValue = '\\x00\\x00'.encode()
        ds.LargestImagePixelValue = '\\xff\\xff'.encode()
        ds.Columns = pixel_array.shape[0]
        ds.Rows = pixel_array.shape[1]
        if pixel_array.dtype != np.uint16:
            pixel_array = pixel_array.astype(np.uint16)
        ds.PixelData = pixel_array.tostring()

        ds.save_as(filename)
        return

    def error_box(self, error_text):
        self.error_popup = Toplevel()
        self.error_popup.geometry("700x30")
        error_label = Label(self.error_popup, text=error_text, font=("Helvetica", 15),
                            background="red")
        error_label.pack()
        self.error_popup.mainloop()


viewer = ViewerMRI()
viewer.gui.mainloop()



